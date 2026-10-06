import SpectralRadiusUpperTail.LowerMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma lower_event_le_centered_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (a ε : ℝ)
    (hm : a-ε/2 ≤ ∫ x, F x ∂μ) :
    μ.real {x | F x < a-ε} ≤ μ.real {x | ε/2 < |F x-∫ y, F y ∂μ|} := by
  apply measureReal_mono (μ := μ)
  intro x hx
  change F x < a-ε at hx
  change ε/2 < |F x-∫ y, F y ∂μ|
  have hh := neg_le_abs (F x-∫ y, F y ∂μ)
  linarith

#print axioms lower_event_le_centered_event
end SpectralRadiusUpperTail
