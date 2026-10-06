import SpectralRadiusUpperTail.LogPolynomialScaling
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- Adding a nonnegative term with a strictly faster exponential rate
does not change the dominant speed-`n` logarithmic rate. -/
theorem log_sum_dominant_rate (a b c : ℕ → ℝ) (L M : ℝ)
    (hapos : ∀ᶠ n in atTop, 0 < a n)
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (hbc : ∀ᶠ n in atTop, b n ≤ c n)
    (ha : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 L))
    (hc : Tendsto (fun n : ℕ => Real.log (c n)/(n : ℝ)) atTop (𝓝 M))
    (hML : M < L) :
    Tendsto (fun n : ℕ => Real.log (a n+b n)/(n : ℝ)) atTop (𝓝 L) := by
  have htwice := log_polynomial_scaling_rate a L 2 0 (by norm_num)
    hapos ha
  have hcomp := hc.eventually_lt ha hML
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ha htwice
  · filter_upwards [hapos, hb, eventually_gt_atTop 0] with n hpa hpb hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hlog := Real.log_le_log hpa (by linarith : a n ≤ a n+b n)
    exact div_le_div_of_nonneg_right hlog hnR.le
  · filter_upwards [hapos, hb, hcpos, hbc, hcomp,
      eventually_gt_atTop 0] with n hpa hpb hpc hbc' hratio hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hm := (div_lt_div_iff₀ hnR hnR).mp hratio
    have hlog : Real.log (c n) < Real.log (a n) := by nlinarith [hm]
    have hca : c n < a n := (Real.log_lt_log_iff hpc hpa).mp hlog
    have hsumpos : 0 < a n+b n := by linarith
    have hupper : a n+b n ≤ 2*a n := by linarith
    have hlogUpper := Real.log_le_log hsumpos hupper
    have hquot := div_le_div_of_nonneg_right hlogUpper hnR.le
    simpa only [pow_zero, div_one] using hquot

#print axioms log_sum_dominant_rate
end SpectralRadiusUpperTail
