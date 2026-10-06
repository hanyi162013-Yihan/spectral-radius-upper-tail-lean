import SpectralRadiusUpperTail.PiNormalizedTilt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_ofReal_probability {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ)
    (hn : ∀ x, 0 ≤ w x) (hp : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (normalizedTilt μ (fun x => ENNReal.ofReal (w x))) := by
  apply normalizedTilt_probability
  · rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hn)]
    exact (ENNReal.ofReal_pos.mpr hp).ne'
  · rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hn)]
    exact ENNReal.ofReal_ne_top

/-- Integration under a normalized nonnegative tilt is the usual ratio of
weighted integrals. No distributional identification is hidden here. -/
theorem integral_normalizedTilt_ofReal {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w f : E → ℝ) (hw : Integrable w μ)
    (hwm : Measurable w) (hn : ∀ x, 0 ≤ w x) (hp : 0 < ∫ x, w x ∂μ) :
    (∫ x, f x ∂normalizedTilt μ (fun x => ENNReal.ofReal (w x))) =
      (∫ x, w x*f x ∂μ)/(∫ x, w x ∂μ) := by
  rw [normalizedTilt_ofReal_eq_density μ w hw hn hp,
    integral_withDensity_eq_integral_toReal_smul
      (hwm.div_const _).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hn _) hp.le), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

lemma integrable_normalizedTilt_ofReal {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w f : E → ℝ) (hw : Integrable w μ)
    (hwm : Measurable w) (hn : ∀ x, 0 ≤ w x) (hp : 0 < ∫ x, w x ∂μ)
    (hf : Integrable (fun x => w x*f x) μ) :
    Integrable f (normalizedTilt μ (fun x => ENNReal.ofReal (w x))) := by
  rw [normalizedTilt_ofReal_eq_density μ w hw hn hp,
    integrable_withDensity_iff_integrable_smul' (hwm.div_const _).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hn _) hp.le), smul_eq_mul]
  simpa only [div_mul_eq_mul_div] using hf.div_const (∫ x, w x ∂μ)

#print axioms integral_normalizedTilt_ofReal
#print axioms integrable_normalizedTilt_ofReal
end SpectralRadiusUpperTail
