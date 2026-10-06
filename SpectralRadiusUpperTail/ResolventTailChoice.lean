import SpectralRadiusUpperTail.ChooseResolventPower

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma resolvent_tail_tendsto (r C : ℝ) (hr : 1 < r) :
    Tendsto (fun k : ℕ => (k+3 : ℝ)*C/r^(k+1)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ)/r^k) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h2 : Tendsto (fun k : ℕ => (3 : ℝ)/r^k) atTop (𝓝 0) := by
    have hh := (tendsto_pow_const_div_const_pow_of_one_lt 0 hr).const_mul 3
    simpa only [pow_zero,mul_zero,mul_one_div] using hh
  have ht := ((h1.add h2).mul_const C).div_const r
  simp only [zero_add,zero_mul,zero_div] at ht
  convert ht using 1
  funext k
  rw [pow_succ]
  ring

lemma exists_small_resolvent_tail (r C ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    ∃ k : ℕ, (k+3 : ℝ)*C/r^(k+1) ≤ ε/2 :=
  ((resolvent_tail_tendsto r C hr).eventually_le_const (by positivity)).exists

#print axioms resolvent_tail_tendsto
#print axioms exists_small_resolvent_tail
end SpectralRadiusUpperTail
