import SpectralRadiusUpperTail.NormProbabilitySum
import Mathlib.Analysis.Normed.Ring.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- A deterministic uniformly bounded factor preserves vanishing norm-tail probabilities. -/
lemma norm_probability_mul_bounded_tendsto
    (Ω E : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, NormedRing (E n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (F : (n : ℕ) → Ω n → E n) (B : (n : ℕ) → E n)
    (hF : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (μ n).real {x | ε ≤ ‖F n x‖}) atTop (𝓝 0))
    (M : ℝ) (hM : 0 < M) (hB : ∀ᶠ n in atTop, ‖B n‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (μ n).real {x | ε ≤ ‖F n x * B n‖}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_
    (hF (ε/M) (div_pos hε hM))
  filter_upwards [hB] with n hn
  refine measureReal_mono (fun x hx => ?_)
  apply (div_le_iff₀ hM).2
  exact hx.trans ((norm_mul_le (F n x) (B n)).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))

#print axioms norm_probability_mul_bounded_tendsto
end SpectralRadiusUpperTail
