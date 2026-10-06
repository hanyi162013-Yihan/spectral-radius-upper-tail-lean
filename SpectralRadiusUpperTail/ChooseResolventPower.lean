import Mathlib.Analysis.SpecificLimits.Normed

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma exists_resolvent_power (r : ℝ) (hr : 1 < r) :
    ∃ m : ℕ, 1 ≤ m ∧ (m+2 : ℝ) ≤ r^m/2 := by
  have h1 : Tendsto (fun m : ℕ => (m : ℝ)/r^m) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h2 : Tendsto (fun m : ℕ => (2 : ℝ)/r^m) atTop (𝓝 0) := by
    have hh := (tendsto_pow_const_div_const_pow_of_one_lt 0 hr).const_mul 2
    simpa only [pow_zero,mul_zero,mul_one_div] using hh
  have ht : Tendsto (fun m : ℕ => (m+2 : ℝ)/r^m) atTop (𝓝 0) := by
    simpa only [zero_add,add_div] using h1.add h2
  obtain ⟨m,hm,hbound⟩ := (eventually_ge_atTop (1 : ℕ)).and
    (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)) |>.exists
  refine ⟨m,hm,?_⟩
  have hpow : 0 < r^m := pow_pos (lt_trans (by norm_num) hr) _
  have hh := (div_le_iff₀ hpow).mp hbound
  linarith

#print axioms exists_resolvent_power
end SpectralRadiusUpperTail
