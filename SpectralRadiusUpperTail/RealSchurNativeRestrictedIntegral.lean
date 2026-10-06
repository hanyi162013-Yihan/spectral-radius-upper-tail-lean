import SpectralRadiusUpperTail.RealSchurNativeGaussianCoordinates
import SpectralRadiusUpperTail.RealArrayGaussianProductMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- Passing to the independent atomic native-block measures does not
change any observable already supported on the atomic product domain. -/
theorem realSchurNativeGaussianProduct_lintegral
    {m : ℕ} (s : Fin m → ℕ) (n : ℝ) (hn : 0 < n)
    (H : ((i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ) → ℝ≥0∞) (hH : Measurable H)
    (hSupport : Function.support H ⊆ Set.pi Set.univ (fun i => realSchurNativeAtomicEntrySet (s i))) :
    (∫⁻ D, ENNReal.ofReal (∏ i : Fin m,
      Real.exp (-(n/2)*∑ ab : Fin (s i) × Fin (s i), (D i ab)^2))*H D) =
        ∫⁻ D, H D ∂Measure.pi (fun i => realSchurNativeGaussianMeasure (s i) n) := by
  let μ := fun i : Fin m => realArrayGaussianMeasure (ι := Fin (s i) × Fin (s i)) n
  let := fun i : Fin m => realArrayGaussianMeasure_finite (ι := Fin (s i) × Fin (s i)) n hn
  let S := Set.pi Set.univ (fun i => realSchurNativeAtomicEntrySet (s i))
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun i => measurableSet_realSchurNativeAtomicEntrySet (s i))
  have hind : S.indicator H=H := by
    funext D
    by_cases hD : D ∈ S
    · exact Set.indicator_of_mem hD H
    · rw [Set.indicator_of_notMem hD]
      symm
      by_contra h
      exact hD (hSupport h)
  rw [← realArrayGaussianMeasure_pi_lintegral (fun i : Fin m => Fin (s i) × Fin (s i)) n hn H hH]
  change (∫⁻ D, H D ∂Measure.pi μ) =
    ∫⁻ D, H D ∂Measure.pi (fun i => (μ i).restrict (realSchurNativeAtomicEntrySet (s i)))
  rw [← Measure.restrict_pi_pi,← lintegral_indicator hS,hind]

#print axioms realSchurNativeGaussianProduct_lintegral
end SpectralRadiusUpperTail
