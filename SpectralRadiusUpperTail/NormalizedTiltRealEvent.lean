import SpectralRadiusUpperTail.NormalizedTiltProductEvent
import SpectralRadiusUpperTail.PositiveWeightNormalizer

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_ofReal_event {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x)
    (hz : 0 < ∫ x, f x ∂μ) (A : Set E) (hA : MeasurableSet A) :
    normalizedTilt μ (fun x => ENNReal.ofReal (f x)) A =
      ENNReal.ofReal ((∫ x in A, f x ∂μ)/(∫ x, f x ∂μ)) := by
  have he := ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn)
  rw [normalizedTilt_event_eq_div _ _ _ hA (by rw [← he]; exact (ENNReal.ofReal_pos.mpr hz).ne'),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hn),
    ← he,ENNReal.ofReal_div_of_pos hz]

#print axioms normalizedTilt_ofReal_event
end SpectralRadiusUpperTail
