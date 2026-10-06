import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma upper_event_le_centered_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (a ε : ℝ)
    (hm : (∫ x, F x ∂μ) ≤ a+ε/2) :
    μ.real {x | a+ε < F x} ≤ μ.real {x | ε/2 < |F x-(∫ y, F y ∂μ)|} := by
  apply measureReal_mono (μ := μ)
  intro x hx
  change a+ε < F x at hx
  change ε/2 < |F x-(∫ y, F y ∂μ)|
  exact lt_of_lt_of_le (by linarith) (le_abs_self _)

#print axioms upper_event_le_centered_event
end SpectralRadiusUpperTail
