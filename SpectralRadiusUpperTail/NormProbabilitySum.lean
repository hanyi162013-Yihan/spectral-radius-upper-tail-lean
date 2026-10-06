import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Vanishing norm-tail probabilities are stable under addition, with varying spaces. -/
lemma norm_probability_add_tendsto
    (Ω E : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, SeminormedAddCommGroup (E n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (F G : (n : ℕ) → Ω n → E n)
    (hF : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {x | ε ≤ ‖F n x‖}) atTop (𝓝 0))
    (hG : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {x | ε ≤ ‖G n x‖}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {x | ε ≤ ‖F n x+G n x‖}) atTop (𝓝 0) := by
  have hlim := (hF (ε/2) (by positivity)).add (hG (ε/2) (by positivity))
  simp only [zero_add] at hlim
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim
  intro n
  apply le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
  intro x hx
  change ε/2 ≤ ‖F n x‖ ∨ ε/2 ≤ ‖G n x‖
  by_contra hh
  push_neg at hh
  have hn := norm_add_le (F n x) (G n x)
  change ε ≤ ‖F n x+G n x‖ at hx
  linarith

#print axioms norm_probability_add_tendsto
end SpectralRadiusUpperTail
