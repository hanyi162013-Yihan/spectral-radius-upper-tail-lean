import SpectralRadiusUpperTail.RealGinibreDominantTailRate
import SpectralRadiusUpperTail.RealGinibreFirstTailSimpleUpper
import SpectralRadiusUpperTail.LogSumDominantRate
import SpectralRadiusUpperTail.ExponentialConstantLogRate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

/-- The integral of the full real one-point expression on the positive
exterior ray has rate `-I₁(r)`. Identification with the matrix eigenvalue
count remains a separate finite-dimensional statement. -/
theorem realGinibreRealTail_log_rate (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log ((∫ x : ℝ in Ioi r, realGinibreDominantDensity n x) +
        (∫ x : ℝ in Ioi r, realGinibreFirstDensity n x))/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  let C : ℝ := 1/(2*(r-1/r))
  have hC : 0 < C := by dsimp [C]; positivity
  have hapos : ∀ᶠ n : ℕ in atTop,
      0 < ∫ x : ℝ in Ioi r, realGinibreDominantDensity n x := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hq := realGinibreCoreDensity_pos n (by omega)
      (r+1) (by linarith)
    have hlow := realGinibreDominantTailLower n hn r 1 hr (by norm_num)
    exact lt_of_lt_of_le (mul_pos (div_pos (by norm_num) hnR) hq) hlow
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ ∫ x : ℝ in Ioi r, realGinibreFirstDensity n x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact (realGinibreFirstDensity_bound n hn x
      (by linarith [show r < x from hx])).1
  have hcpos : ∀ᶠ n : ℕ in atTop,
      0 < C*Real.exp (-(n : ℝ)*rate 2 r) :=
    Filter.Eventually.of_forall (fun n => mul_pos hC (Real.exp_pos _))
  have hbc : ∀ᶠ n : ℕ in atTop,
      (∫ x : ℝ in Ioi r, realGinibreFirstDensity n x) ≤
        C*Real.exp (-(n : ℝ)*rate 2 r) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact realGinibreFirstTailSimpleUpper n hn r hr
  have hfast : -rate 2 r < -rate 1 r := by
    rw [rate_two_eq]
    have hp := rate_pos 1 r (by norm_num) hr
    linarith
  exact log_sum_dominant_rate
    (fun n : ℕ => ∫ x : ℝ in Ioi r, realGinibreDominantDensity n x)
    (fun n : ℕ => ∫ x : ℝ in Ioi r, realGinibreFirstDensity n x)
    (fun n : ℕ => C*Real.exp (-(n : ℝ)*rate 2 r))
    (-rate 1 r) (-rate 2 r) hapos hb hcpos hbc
    (realGinibreDominantTail_log_rate r hr)
    (exponential_constant_log_rate C (rate 2 r) hC) hfast

#print axioms realGinibreRealTail_log_rate
end SpectralRadiusUpperTail
