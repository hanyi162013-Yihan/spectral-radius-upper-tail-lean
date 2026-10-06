import SpectralRadiusUpperTail.HaarSphereDirection
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma haar_polar_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) = ∫⁻ p : sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
      f (p.2.val • p.1.val) ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)) := by
  have hp : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    have hh := measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl
    simpa only [restrict_compl_singleton] using hh
  rw [← hp.lintegral_comp hf]
  have ht := μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp
    (hf.comp (measurable_subtype_coe.comp (homeomorphUnitSphereProd E).symm.measurable))
  simp only [Function.comp_def] at ht
  simp only [Homeomorph.symm_apply_apply] at ht
  simpa only [homeomorphUnitSphereProd_symm_apply_coe] using ht

#print axioms haar_polar_lintegral
end SpectralRadiusUpperTail
