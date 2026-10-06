import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

/-- Open right tails determine a finite real measure. The comparison
measure need not be known finite before the equality is proved. -/
theorem realMeasure_eq_of_open_tails (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (h : ∀ b : ℝ, μ (Ioi b) = ν (Ioi b)) : μ = ν := by
  apply Measure.ext_of_Ioc' μ ν (fun _ _ _ => measure_ne_top _ _)
  intro a b hab
  rw [← Ioi_sdiff_Ioi,
    measure_sdiff (Ioi_subset_Ioi hab.le) nullMeasurableSet_Ioi (measure_ne_top μ _),
    measure_sdiff (Ioi_subset_Ioi hab.le) nullMeasurableSet_Ioi
      (show ν (Ioi b) ≠ ∞ by rw [← h b]; exact measure_ne_top _ _),
    h a, h b]

#print axioms realMeasure_eq_of_open_tails
end SpectralRadiusUpperTail
