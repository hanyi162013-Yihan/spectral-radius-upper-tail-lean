import SpectralRadiusUpperTail.ExponentialPrefactorBudget

namespace SpectralRadiusUpperTail
open Filter

lemma eventually_exponential_difference_lower (a b ε : ℝ) (hba : b < a) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(a-ε)) ≤ Real.exp ((n : ℝ)*a)-Real.exp ((n : ℝ)*b) := by
  have h1 := eventually_exp_prefactor_absorb 2 b (a-b) (by norm_num) (sub_pos.mpr hba)
  have h2 := eventually_exp_prefactor_absorb 2 (a-ε) ε (by norm_num) hε
  filter_upwards [h1, h2] with n hn hm
  have he1 : b+(a-b)=a := by ring
  have he2 : a-ε+ε=a := by ring
  rw [he1] at hn
  rw [he2] at hm
  linarith

#print axioms eventually_exponential_difference_lower
end SpectralRadiusUpperTail
