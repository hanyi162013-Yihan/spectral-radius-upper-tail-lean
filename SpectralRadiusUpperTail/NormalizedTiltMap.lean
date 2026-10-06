import SpectralRadiusUpperTail.NormalizedTiltProductEvent
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_map_measurePreserving {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (f : X → Y) (hf : MeasurePreserving f μ ν) (w : Y → ℝ≥0∞) (hw : Measurable w)
    (hZ : (∫⁻ y, w y ∂ν) ≠ 0) :
    (normalizedTilt μ (fun x => w (f x))).map f = normalizedTilt ν w := by
  have he := hf.lintegral_comp hw
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hf.measurable hA,
    normalizedTilt_event_eq_div _ _ _ (hA.preimage hf.measurable) (by rwa [he]),
    normalizedTilt_event_eq_div _ _ _ hA hZ,he,hf.setLIntegral_comp_preimage hA hw]

#print axioms normalizedTilt_map_measurePreserving
end SpectralRadiusUpperTail
