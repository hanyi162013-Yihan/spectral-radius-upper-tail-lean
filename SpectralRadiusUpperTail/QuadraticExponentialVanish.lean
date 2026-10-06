import SpectralRadiusUpperTail.ExponentialPrefactorBudget

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma quadratic_exponential_tendsto_zero (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q) :
    Tendsto (fun n : ℕ => C*Real.exp (-q*(n : ℝ)^2)) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => by positivity)) _ he
  simpa only [mul_neg_one] using eventually_quadratic_exp_le_linear C q (-1) hC hq

lemma eventually_quadratic_exponential_le (C q ε : ℝ) (hC : 0 ≤ C)
    (hq : 0 < q) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp (-q*(n : ℝ)^2) ≤ ε := by
  exact ((tendsto_order.mp (quadratic_exponential_tendsto_zero C q hC hq)).2 ε hε).mono (fun _ h => h.le)

#print axioms quadratic_exponential_tendsto_zero
#print axioms eventually_quadratic_exponential_le
end SpectralRadiusUpperTail
