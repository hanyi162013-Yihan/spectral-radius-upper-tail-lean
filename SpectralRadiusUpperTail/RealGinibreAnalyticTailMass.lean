import SpectralRadiusUpperTail.RealGinibreRealTailRate
import SpectralRadiusUpperTail.RealGinibreNonrealTailSimpleUpper
import SpectralRadiusUpperTail.LogSumDominantRate
import SpectralRadiusUpperTail.ExponentialConstantLogRate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set Metric
open scoped Topology

noncomputable def realGinibreRealPositiveTailMass (n : ℕ) (r : ℝ) : ℝ :=
  (∫ x : ℝ in Ioi r, realGinibreDominantDensity n x) +
    (∫ x : ℝ in Ioi r, realGinibreFirstDensity n x)

noncomputable def realGinibreNonrealExteriorMass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ z : ℂ in {z | r < ‖z‖}, realGinibreNonrealDensityAt n z

theorem realGinibreRealPositiveTailMass_pos (n : ℕ) (hn : 3 ≤ n)
    (r : ℝ) (hr : 1 < r) :
    0 < realGinibreRealPositiveTailMass n r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hq := realGinibreCoreDensity_pos n (by omega)
    (r+1) (by linarith)
  have hlow := realGinibreDominantTailLower n hn r 1 hr (by norm_num)
  have hdom : 0 < ∫ x : ℝ in Ioi r, realGinibreDominantDensity n x :=
    lt_of_lt_of_le (mul_pos (div_pos (by norm_num) hnR) hq) hlow
  have hfirst : 0 ≤ ∫ x : ℝ in Ioi r, realGinibreFirstDensity n x := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact (realGinibreFirstDensity_bound n (by omega) x
      (by linarith [show r < x from hx])).1
  unfold realGinibreRealPositiveTailMass
  linarith

theorem realGinibreNonrealExteriorMass_nonneg (n : ℕ)
    (r : ℝ) (hr : 1 < r) :
    0 ≤ realGinibreNonrealExteriorMass n r := by
  unfold realGinibreNonrealExteriorMass
  apply setIntegral_nonneg
    (measurableSet_lt measurable_const measurable_norm)
  intro z hz
  exact (realGinibreNonrealDensityAt_bound n z
    (by linarith [show r < ‖z‖ from hz])).1

theorem eventually_realGinibreRadialCondition (r : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, 1/r ≤ (n : ℝ)*(r-1/r) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ)*(r-1/r)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hs
  exact ht.eventually (eventually_ge_atTop (1/r))

/-- The sum of the positive-real and nonreal exterior one-point masses
still has the real-eigenvalue exponent. -/
theorem realGinibreAnalyticTailMass_log_rate (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (realGinibreRealPositiveTailMass n r +
        realGinibreNonrealExteriorMass n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  let C : ℝ := 2*r/(r-1/r)
  have hC : 0 < C := by dsimp [C]; positivity
  have hapos : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreRealPositiveTailMass n r := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact realGinibreRealPositiveTailMass_pos n hn r hr
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ realGinibreNonrealExteriorMass n r :=
    Filter.Eventually.of_forall (fun n =>
      realGinibreNonrealExteriorMass_nonneg n r hr)
  have hcpos : ∀ᶠ n : ℕ in atTop,
      0 < C*Real.exp (-(n : ℝ)*rate 2 r) :=
    Filter.Eventually.of_forall (fun n => mul_pos hC (Real.exp_pos _))
  have hbc : ∀ᶠ n : ℕ in atTop,
      realGinibreNonrealExteriorMass n r ≤
        C*Real.exp (-(n : ℝ)*rate 2 r) := by
    filter_upwards [eventually_realGinibreRadialCondition r hr,
      eventually_gt_atTop 0] with n hnrad hnpos
    exact realGinibreNonrealTailSimpleUpper n r hr hnpos hnrad
  have hfast : -rate 2 r < -rate 1 r := by
    rw [rate_two_eq]
    have hp := rate_pos 1 r (by norm_num) hr
    linarith
  exact log_sum_dominant_rate
    (fun n => realGinibreRealPositiveTailMass n r)
    (fun n => realGinibreNonrealExteriorMass n r)
    (fun n => C*Real.exp (-(n : ℝ)*rate 2 r))
    (-rate 1 r) (-rate 2 r) hapos hb hcpos hbc
    (by simpa only [realGinibreRealPositiveTailMass] using
      realGinibreRealTail_log_rate r hr)
    (exponential_constant_log_rate C (rate 2 r) hC) hfast

#print axioms realGinibreRealPositiveTailMass_pos
#print axioms realGinibreNonrealExteriorMass_nonneg
#print axioms eventually_realGinibreRadialCondition
#print axioms realGinibreAnalyticTailMass_log_rate
end SpectralRadiusUpperTail
