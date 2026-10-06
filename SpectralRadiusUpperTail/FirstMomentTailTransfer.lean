import SpectralRadiusUpperTail.LogPolynomialScaling
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- A count-event probability squeezed between a first moment divided
by `n` and twice a full first moment has the common exponential rate. -/
theorem first_moment_tail_transfer (a b q : ℕ → ℝ) (L : ℝ)
    (haPos : ∀ᶠ n in atTop, 0 < a n)
    (hbPos : ∀ᶠ n in atTop, 0 < b n)
    (ha : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ)) atTop (𝓝 L))
    (hb : Tendsto (fun n : ℕ => Real.log (b n)/(n : ℝ)) atTop (𝓝 L))
    (hlow : ∀ᶠ n : ℕ in atTop, a n/(n : ℝ) ≤ q n)
    (hupp : ∀ᶠ n : ℕ in atTop, q n ≤ 2*b n) :
    Tendsto (fun n : ℕ => Real.log (q n)/(n : ℝ)) atTop (𝓝 L) := by
  have hlowRate := log_polynomial_scaling_rate a L 1 1
    (by norm_num) haPos ha
  have huppRate := log_polynomial_scaling_rate b L 2 0
    (by norm_num) hbPos hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowRate huppRate
  · filter_upwards [haPos, hlow, eventually_gt_atTop 0] with n han hqn hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hlog := Real.log_le_log (div_pos han hnR) hqn
    simpa only [pow_one, one_mul] using
      div_le_div_of_nonneg_right hlog hnR.le
  · filter_upwards [haPos, hbPos, hlow, hupp,
      eventually_gt_atTop 0] with n han hbn hqn hupper hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hqpos : 0 < q n := lt_of_lt_of_le (div_pos han hnR) hqn
    have hlog := Real.log_le_log hqpos hupper
    simpa only [pow_zero, div_one] using
      div_le_div_of_nonneg_right hlog hnR.le

#print axioms first_moment_tail_transfer
end SpectralRadiusUpperTail
