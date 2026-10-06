import SpectralRadiusUpperTail.GaussianMarkedRealTailBounds
import SpectralRadiusUpperTail.RealGinibreCoreMovingRate
import SpectralRadiusUpperTail.LogPolynomialScaling
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

/-- The tail integral of the marked-eigenline *candidate* has the sharp
real-Ginibre speed-`n` rate. The only missing probabilistic identification is
the global marked-eigenline count formula. -/
theorem gaussianMarkedRealDensity_tail_log_rate
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hrpos : 0 < r := by linarith
  have hs : 0 < r-1/r := by
    have hsq : 1 < r^2 := by nlinarith
    apply sub_pos.mpr
    apply (div_lt_iff₀ hrpos).mpr
    nlinarith
  have hc : 0 < 1/(r-1/r) := by positivity
  have hqLower : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreCoreDensity n (r+1/(n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact realGinibreCoreDensity_pos n hn _ (by positivity)
  have hqUpper : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreCoreDensity n r := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact realGinibreCoreDensity_pos n hn r hrpos
  have hlow := log_polynomial_scaling_rate
    (fun n : ℕ => realGinibreCoreDensity n (r+1/(n : ℝ)))
    (-rate 1 r) 1 1 (by norm_num) hqLower
    (realGinibreCoreDensity_moving_log_rate r hrpos)
  have hupp := log_polynomial_scaling_rate
    (fun n : ℕ => realGinibreCoreDensity n r)
    (-rate 1 r) (1/(r-1/r)) 0 hc hqUpper
    (realGinibreCoreDensity_log_rate r hrpos)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hδ : 0 < (1 : ℝ)/(n : ℝ) := by positivity
    have hq := realGinibreCoreDensity_pos n hn (r+1/(n : ℝ)) (by positivity)
    have hbound := gaussianMarkedRealDensity_tail_lower n hn r (1/(n : ℝ)) hr hδ
    have hloweq : (1/(n : ℝ))*
        realGinibreCoreDensity n (r+1/(n : ℝ)) =
      realGinibreCoreDensity n (r+1/(n : ℝ))/(n : ℝ) := by ring
    rw [hloweq] at hbound
    have hlowpos : 0 < realGinibreCoreDensity n (r+1/(n : ℝ))/(n : ℝ) :=
      div_pos hq hnR
    have hlog := Real.log_le_log hlowpos hbound
    simpa only [pow_one, one_mul] using div_le_div_of_nonneg_right hlog hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hδ : 0 < (1 : ℝ)/(n : ℝ) := by positivity
    have hq := realGinibreCoreDensity_pos n hn (r+1/(n : ℝ)) (by positivity)
    have hboundLow := gaussianMarkedRealDensity_tail_lower n hn r (1/(n : ℝ)) hr hδ
    have hMpos : 0 < (∫ x : ℝ in Ioi r, gaussianMarkedRealDensity n x) :=
      lt_of_lt_of_le (mul_pos hδ hq) hboundLow
    have hbound := gaussianMarkedRealDensity_tail_upper n hn r hr
    have huppEq : realGinibreCoreDensity n r / (r-1/r) =
        (1/(r-1/r))*realGinibreCoreDensity n r/(n : ℝ)^0 := by
      simp only [pow_zero, div_one]
      ring
    rw [huppEq] at hbound
    have hlog := Real.log_le_log hMpos hbound
    exact div_le_div_of_nonneg_right hlog hnR.le

#print axioms gaussianMarkedRealDensity_tail_log_rate
end SpectralRadiusUpperTail
