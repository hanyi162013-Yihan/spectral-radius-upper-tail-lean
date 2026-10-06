import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The area formula on any measurable injective domain of the actual
Schur map. The domain need not lie inside an inverse-function chart. -/
theorem realSchurMixed_lintegral_injective_rotated
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (hQ : Qᵀ*Q=1)
    (U : Set (RealSchurMixedTangent s)) (hU : MeasurableSet U)
    (hinj : Set.InjOn (realSchurMixedRotatedEntryCoordinates s T Q hQ) U)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRotatedEntryCoordinates s T Q hQ '' U,
        g y ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in U, ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
        g (realSchurMixedRotatedEntryCoordinates s T Q hQ x)
        ∂realSchurMixedCoordinateVolume s := by
  let E := realSchurMixedOutputCoordinateEquiv s Q hQ
  have hbase : Set.InjOn (realSchurMixedEntryCoordinates s T) U := by
    intro x hx y hy hxy
    exact hinj hx hy (congrArg E hxy)
  have harea := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (realSchurMixedCoordinateVolume s) hU
    (fun x _ => (realSchurMixedEntryCoordinates_differentiable s T x).hasFDerivAt.hasFDerivWithinAt)
    hbase (fun y => g (E y))
  simp only [← realSchurMixedJacobianWeight_eq_abs_det s hs T hT] at harea
  have hrot := (realSchurMixedOutputCoordinateEquiv_measurePreserving s Q hQ).setLIntegral_comp_emb
    E.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding g
    (realSchurMixedEntryCoordinates s T '' U)
  rw [harea] at hrot
  change (∫⁻ y in (fun x => E (realSchurMixedEntryCoordinates s T x)) '' U,
      g y ∂realSchurMixedCoordinateVolume s) =
    ∫⁻ x in U, ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
      g (E (realSchurMixedEntryCoordinates s T x)) ∂realSchurMixedCoordinateVolume s
  simpa only [Set.image_image, Function.comp_def] using hrot.symm

/-- Exact Gaussian change of variables on complete-fiber domains,
once their injectivity has been proved by spectral classification. -/
theorem realSchurMixed_gaussian_lintegral_injective_rotated
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (hQ : Qᵀ*Q=1)
    (U : Set (RealSchurMixedTangent s)) (hU : MeasurableSet U)
    (hinj : Set.InjOn (realSchurMixedRotatedEntryCoordinates s T Q hQ) U)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRotatedEntryCoordinates s T Q hQ '' U,
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g y
        ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in U, ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
        (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) (T+x.2.val)) *
          g (realSchurMixedRotatedEntryCoordinates s T Q hQ x))
        ∂realSchurMixedCoordinateVolume s := by
  have h := realSchurMixed_lintegral_injective_rotated s hs T Q hT hQ U hU hinj
    (fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g y)
  simpa only [realSchurMixedGaussianCoordinateWeight_rotated_chart] using h

#print axioms realSchurMixed_lintegral_injective_rotated
#print axioms realSchurMixed_gaussian_lintegral_injective_rotated
end SpectralRadiusUpperTail
