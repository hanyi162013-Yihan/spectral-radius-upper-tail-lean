import SpectralRadiusUpperTail.GaussianMarkedRealTailRate
import SpectralRadiusUpperTail.RealGinibreAnalyticTailMass
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set Metric
open scoped Topology

/-- Positive-real exterior mass predicted by the marked-eigenline Jacobian,
with the Gaussian determinant expectation evaluated under the actual iid law. -/
noncomputable def gaussianMarkedRealTailMass (n : ℕ) (r : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x

theorem gaussianMarkedRealTailMass_pos
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 1 < r) :
    0 < gaussianMarkedRealTailMass n r := by
  have hq := realGinibreCoreDensity_pos n hn (r+1) (by linarith)
  have hlow := gaussianMarkedRealDensity_tail_lower n hn r 1 hr (by norm_num)
  unfold gaussianMarkedRealTailMass
  have h : 0 < 1 * realGinibreCoreDensity n (r+1) := by simpa using hq
  exact lt_of_lt_of_le h hlow

theorem gaussianMarkedRealTailMass_log_rate
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (gaussianMarkedRealTailMass n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  simpa only [gaussianMarkedRealTailMass] using
    gaussianMarkedRealDensity_tail_log_rate r hr

/-- The nonreal analytic exterior mass decays at the faster complex rate;
adding it does not alter the marked-real candidate's exponential rate. -/
theorem gaussianMarkedRealPlusNonrealMass_log_rate
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (gaussianMarkedRealTailMass n r +
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
      0 < gaussianMarkedRealTailMass n r := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact gaussianMarkedRealTailMass_pos n hn r hr
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
    (fun n => gaussianMarkedRealTailMass n r)
    (fun n => realGinibreNonrealExteriorMass n r)
    (fun n => C*Real.exp (-(n : ℝ)*rate 2 r))
    (-rate 1 r) (-rate 2 r) hapos hb hcpos hbc
    (gaussianMarkedRealTailMass_log_rate r hr)
    (exponential_constant_log_rate C (rate 2 r) hC) hfast

#print axioms gaussianMarkedRealTailMass_pos
#print axioms gaussianMarkedRealTailMass_log_rate
#print axioms gaussianMarkedRealPlusNonrealMass_log_rate
end SpectralRadiusUpperTail
