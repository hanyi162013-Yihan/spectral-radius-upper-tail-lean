import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Map

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Outer-event domination needs no measurability of the event itself. -/
lemma event_probability_le_of_map {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Ω → E) (hf : AEMeasurable f μ) (hmap : μ.map f = ν) (S : Set E) :
    μ.real (f ⁻¹' S) ≤ ν.real S := by
  change (μ (f ⁻¹' S)).toReal ≤ (ν S).toReal
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [← hmap]
  exact Measure.le_map_apply hf S

#print axioms event_probability_le_of_map
end SpectralRadiusUpperTail
