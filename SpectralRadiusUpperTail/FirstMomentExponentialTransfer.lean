import SpectralRadiusUpperTail.LogPolynomialScaling
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- A first-moment lower bound and an exponential upper bound with the same
speed-n exponent determine the exact logarithmic probability rate. -/
theorem firstMomentLower_exponentialUpper_logRate
    (a q : ℕ → ℝ) (L : ℝ)
    (haPos : ∀ᶠ n : ℕ in atTop, 0 < a n)
    (haRate : Tendsto (fun n : ℕ => Real.log (a n)/(n : ℝ))
      atTop (𝓝 L))
    (hlower : ∀ᶠ n : ℕ in atTop, a n/(n : ℝ) ≤ q n)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      q n ≤ Real.exp ((n : ℝ)*(L+ε))) :
    Tendsto (fun n : ℕ => Real.log (q n)/(n : ℝ))
      atTop (𝓝 L) := by
  have hlowRate : Tendsto
      (fun n : ℕ => Real.log (a n/(n : ℝ))/(n : ℝ))
      atTop (𝓝 L) := by
    simpa only [one_mul, pow_one] using
      log_polynomial_scaling_rate a L 1 1 (by norm_num) haPos haRate
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlowε := (tendsto_order.mp hlowRate).1 (L-ε/2) (by linarith)
  filter_upwards [hlowε, hupper (ε/2) (by positivity),
    hlower, haPos, eventually_gt_atTop 0] with n hnlow hnupper hncomp han hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hqpos : 0 < q n := lt_of_lt_of_le (div_pos han hnR) hncomp
  have hloglow : Real.log (a n/(n : ℝ)) ≤ Real.log (q n) :=
    Real.log_le_log (div_pos han hnR) hncomp
  have hlogupper : Real.log (q n) ≤ (n : ℝ)*(L+ε/2) := by
    have h := Real.log_le_log hqpos hnupper
    rwa [Real.log_exp] at h
  have hlowdiv := div_le_div_of_nonneg_right hloglow hnR.le
  have huppdiv : Real.log (q n)/(n : ℝ) ≤ L+ε/2 :=
    (div_le_iff₀ hnR).2 (by simpa [mul_comm] using hlogupper)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

#print axioms firstMomentLower_exponentialUpper_logRate
end SpectralRadiusUpperTail
