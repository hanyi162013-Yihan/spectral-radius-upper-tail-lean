import SpectralRadiusUpperTail.RealSchurMixedCodeImageMultiplicity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator BigOperators

/-- The actual Gaussian area formula, normalized across every spectral
code of one shape. Each matrix represented by that shape is counted once.
The remaining reciprocal overlap factor is intrinsic to the upper matrix. -/
theorem realSchurMixed_normalized_gaussian_lintegral
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (g : RealSchurMixedTangent s → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in ⋃ code, ⋃ k,
        realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
          realSchurMixedFlagCodedSource s hs c hc R k code,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g y
        ∂realSchurMixedCoordinateVolume s) =
      ∑ code, ∑' k, ∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
        ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
          (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) *
            ((realSchurMixedCodeMultiplicity s x.2.val)⁻¹ *
              g (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property x)))
          ∂realSchurMixedCoordinateVolume s := by
  classical
  let C := fun code => ⋃ k,
    realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
      realSchurMixedFlagCodedSource s hs c hc R k code
  have hC : ∀ code, MeasurableSet (C code) := fun code =>
    MeasurableSet.iUnion (fun k => measurableSet_realSchurMixedFlagCodedImage s hs c hc R k code)
  let f := fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g y
  have hW : Continuous (realMatrixGaussianWeight (RealSchurMixedCoord s)) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hf : Measurable f :=
    (hW.comp (realSchurMixedEntryEquiv s).symm.toContinuousLinearEquiv.continuous).measurable.ennreal_ofReal.mul hg
  have hnorm := lintegral_finiteCover_normalized C hC (realSchurMixedCoordinateVolume s) f hf
  refine hnorm.symm.trans ?_
  apply Finset.sum_congr rfl
  intro code _
  let g' := fun y => (realSchurMixedCodeMultiplicity s ((realSchurMixedEntryEquiv s).symm y))⁻¹*g y
  have hweight : (∫⁻ y in C code, (finiteCoverMultiplicity C y)⁻¹*f y
      ∂realSchurMixedCoordinateVolume s) =
      ∫⁻ y in C code, ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g' y
        ∂realSchurMixedCoordinateVolume s := by
    apply lintegral_congr
    intro y
    have hM := realSchurMixedCodeImageMultiplicity_eq s hs c hc R hcover y
    change finiteCoverMultiplicity C y=realSchurMixedCodeMultiplicity s
      ((realSchurMixedEntryEquiv s).symm y) at hM
    dsimp only [f,g']
    rw [hM]
    ac_rfl
  rw [hweight,realSchurMixedFlagCoded_gaussian_lintegral s hs c hc R code g']
  apply tsum_congr
  intro k
  apply lintegral_congr
  intro x
  dsimp only [g']
  rw [realSchurMixedCodeMultiplicity_chart]

#print axioms realSchurMixed_normalized_gaussian_lintegral
end SpectralRadiusUpperTail
