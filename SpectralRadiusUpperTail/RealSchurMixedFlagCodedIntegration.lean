import SpectralRadiusUpperTail.RealSchurMixedFlagCodedSource
import SpectralRadiusUpperTail.RealSchurMixedInjectiveIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurMixedRotatedEntryCoordinates_differentiable
    {m : ℕ} (s : Fin m → ℕ)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) :
    Differentiable ℝ (realSchurMixedRotatedEntryCoordinates s T Q hQ) :=
  (realSchurMixedOutputCoordinateEquiv s Q hQ).toContinuousLinearEquiv.differentiable.comp
    (realSchurMixedEntryCoordinates_differentiable s T)

theorem realSchurMixedFlagCodedSource_injOn
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set.InjOn (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property)
      (realSchurMixedFlagCodedSource s hs c hc R k code) := by
  intro x hx y hy heq
  exact (realSchurMixedFlagCodedSource_unique s hs c hc R k k code x y hx hy heq).2

theorem measurableSet_realSchurMixedFlagCodedImage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
      realSchurMixedFlagCodedSource s hs c hc R k code) := by
  exact measurable_image_of_fderivWithin
    (measurableSet_realSchurMixedFlagCodedSource s hs c hc R k code)
    (fun x _ => (realSchurMixedRotatedEntryCoordinates_differentiable s 0
      (R k).val (R k).property x).hasFDerivAt.hasFDerivWithinAt)
    (realSchurMixedFlagCodedSource_injOn s hs c hc R k code)

theorem pairwise_realSchurMixedFlagCodedImage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Pairwise (fun k l => Disjoint
      (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurMixedFlagCodedSource s hs c hc R k code)
      (realSchurMixedRotatedEntryCoordinates s 0 (R l).val (R l).property ''
        realSchurMixedFlagCodedSource s hs c hc R l code)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  exact hkl (realSchurMixedFlagCodedSource_unique s hs c hc R k l code x y hx hy
    (hxz.trans hyz.symm)).1

/-- Exact Gaussian area formula for one finite spectral class, summed
over the disjoint angle patches. Every source retains its full strict-
upper Gaussian fiber. Different spectral classes are not identified here. -/
theorem realSchurMixedFlagCoded_gaussian_lintegral
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    (∫⁻ y in ⋃ k, realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurMixedFlagCodedSource s hs c hc R k code,
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight s y)*g y
        ∂realSchurMixedCoordinateVolume s) =
      ∑' k, ∫⁻ x in realSchurMixedFlagCodedSource s hs c hc R k code,
        ENNReal.ofReal (realSchurMixedJacobianWeight s 0 x) *
          (ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord s) x.2.val) *
            g (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property x))
          ∂realSchurMixedCoordinateVolume s := by
  rw [lintegral_iUnion (fun k => measurableSet_realSchurMixedFlagCodedImage s hs c hc R k code)
    (pairwise_realSchurMixedFlagCodedImage s hs c hc R code)]
  congr 1
  funext k
  simpa only [zero_add] using realSchurMixed_gaussian_lintegral_injective_rotated s hs
    0 (R k).val (map_zero _) (R k).property
    (realSchurMixedFlagCodedSource s hs c hc R k code)
    (measurableSet_realSchurMixedFlagCodedSource s hs c hc R k code)
    (realSchurMixedFlagCodedSource_injOn s hs c hc R k code) g

#print axioms realSchurMixedRotatedEntryCoordinates_differentiable
#print axioms realSchurMixedFlagCodedSource_injOn
#print axioms measurableSet_realSchurMixedFlagCodedImage
#print axioms pairwise_realSchurMixedFlagCodedImage
#print axioms realSchurMixedFlagCoded_gaussian_lintegral
end SpectralRadiusUpperTail
