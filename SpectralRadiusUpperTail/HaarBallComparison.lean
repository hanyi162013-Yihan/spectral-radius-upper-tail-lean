import SpectralRadiusUpperTail.HaarPolarIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma sphere_radial_integral_lower (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f)
    (hmono : ∀ v : sphere (0 : E) 1, ∀ r : ℝ, 0 < r → r < 1 → f v.val ≤ f (r • v.val)) :
    (∫⁻ v : sphere (0 : E) 1, f v.val ∂μ.toSphere) *
      (Measure.volumeIoiPow (Module.finrank ℝ E-1)) (Set.Iio ⟨1,by norm_num⟩) ≤ ∫⁻ x, f x ∂μ := by
  let σ := Measure.volumeIoiPow (Module.finrank ℝ E-1)
  let J : Set (Set.Ioi (0 : ℝ)) := Set.Iio ⟨1,by norm_num⟩
  have hm : Measurable (fun p : sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => f (p.2.val • p.1.val)) := by
    exact hf.comp (by fun_prop)
  rw [haar_polar_lintegral μ f hf,lintegral_prod _ hm.aemeasurable]
  have hv : Measurable (fun v : sphere (0 : E) 1 => f v.val) := hf.comp measurable_subtype_coe
  rw [← lintegral_mul_const _ hv]
  apply lintegral_mono
  intro v
  calc
    f v.val * σ J = ∫⁻ r in J, f v.val ∂σ := by simp
    _ ≤ ∫⁻ r in J, f (r.val • v.val) ∂σ := by
      apply setLIntegral_mono' measurableSet_Iio
      intro r hr
      exact hmono v r.val r.property hr
    _ ≤ ∫⁻ r, f (r.val • v.val) ∂σ := setLIntegral_le_lintegral _ _

#print axioms sphere_radial_integral_lower
end SpectralRadiusUpperTail
