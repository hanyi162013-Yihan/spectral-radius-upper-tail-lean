import SpectralRadiusUpperTail.LogQuarterRate
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma logQuarterRate_inv_sqrt_eventually :
    ∀ᶠ n : ℕ in atTop, 1/Real.sqrt (n : ℝ) ≤ logQuarterRate n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with n hl hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn'
  have hx : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by simpa using Real.sqrt_le_sqrt hl
  have hx3 : 1 ≤ (Real.sqrt (Real.log (n : ℝ)))^3 := by
    calc
      1 = (1 : ℝ)^3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hx 3
  have he := logQuarterRate_square n hn
  have hr := logQuarterRate_nonneg n hn
  have hp : 1 ≤ (logQuarterRate n*Real.sqrt (n : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_right hx3 (Real.sqrt_nonneg (n : ℝ))
    rw [← he] at hh
    nlinarith
  have hmul : 1 ≤ logQuarterRate n*Real.sqrt (n : ℝ) := by
    have := mul_nonneg hr (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  exact (div_le_iff₀ (by linarith : 0 < Real.sqrt (n : ℝ))).2 hmul

#print axioms logQuarterRate_inv_sqrt_eventually
end SpectralRadiusUpperTail
