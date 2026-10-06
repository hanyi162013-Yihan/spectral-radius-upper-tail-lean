import SpectralRadiusUpperTail.RealGinibreDominantTailUpper
import SpectralRadiusUpperTail.RealGinibreDominantTailLower
import SpectralRadiusUpperTail.RealGinibreCoreMovingRate
import SpectralRadiusUpperTail.LogPolynomialScaling
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

/-- The integrated dominant real-eigenvalue one-point term has the sharp
speed-`n` rate. This uses only explicit scalar Gamma/Poisson estimates and
does not invoke a Gaussian spectral-radius LDP. -/
theorem realGinibreDominantTail_log_rate (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (∫ x : ℝ in Ioi r, realGinibreDominantDensity n x)/(n : ℝ))
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
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    exact realGinibreCoreDensity_pos n (by omega) _ (by positivity)
  have hqUpper : ∀ᶠ n : ℕ in atTop,
      0 < realGinibreCoreDensity n r := by
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact realGinibreCoreDensity_pos n (by omega) r hrpos
  have hlow := log_polynomial_scaling_rate
    (fun n : ℕ => realGinibreCoreDensity n (r+1/(n : ℝ)))
    (-rate 1 r) 1 2 (by norm_num) hqLower
    (realGinibreCoreDensity_moving_log_rate r hrpos)
  have hupp := log_polynomial_scaling_rate
    (fun n : ℕ => realGinibreCoreDensity n r)
    (-rate 1 r) (1/(r-1/r)) 1 hc hqUpper
    (realGinibreCoreDensity_log_rate r hrpos)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hδ : 0 < (1 : ℝ)/(n : ℝ) := by positivity
    have hq := realGinibreCoreDensity_pos n hnpos (r+1/(n : ℝ)) (by positivity)
    have hbound := realGinibreDominantTailLower n hn r (1/(n : ℝ)) hr hδ
    have hloweq : ((1/(n : ℝ))/(n : ℝ))*
        realGinibreCoreDensity n (r+1/(n : ℝ)) =
      realGinibreCoreDensity n (r+1/(n : ℝ))/(n : ℝ)^2 := by
      field_simp [hnR.ne']
    rw [hloweq] at hbound
    have hlowpos : 0 < realGinibreCoreDensity n (r+1/(n : ℝ))/(n : ℝ)^2 :=
      div_pos hq (by positivity)
    have hlog := Real.log_le_log hlowpos hbound
    simpa only [one_mul] using div_le_div_of_nonneg_right hlog hnR.le
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hδ : 0 < (1 : ℝ)/(n : ℝ) := by positivity
    have hq := realGinibreCoreDensity_pos n hnpos (r+1/(n : ℝ)) (by positivity)
    have hboundLow := realGinibreDominantTailLower n hn r (1/(n : ℝ)) hr hδ
    have hMpos : 0 < (∫ x : ℝ in Ioi r, realGinibreDominantDensity n x) :=
      lt_of_lt_of_le (mul_pos (div_pos hδ hnR) hq) hboundLow
    have hbound := realGinibreDominantTailUpper n hn r hr
    have huppEq : realGinibreCoreDensity n r / ((n : ℝ)*(r-1/r)) =
        (1/(r-1/r))*realGinibreCoreDensity n r/(n : ℝ) := by
      field_simp [hnR.ne', ne_of_gt hs]
    rw [huppEq] at hbound
    have hlog := Real.log_le_log hMpos hbound
    simpa only [pow_one] using div_le_div_of_nonneg_right hlog hnR.le

#print axioms realGinibreDominantTail_log_rate
end SpectralRadiusUpperTail
