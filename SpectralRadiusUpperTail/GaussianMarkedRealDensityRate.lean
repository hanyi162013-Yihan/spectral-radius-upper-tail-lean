import SpectralRadiusUpperTail.GaussianMarkedRealDensitySandwich
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The candidate obtained from the actual Gaussian shifted-determinant
moment has the sharp real-Ginibre pointwise speed-`n` rate.  Identifying this
candidate with the matrix eigenvalue intensity still requires the geometric
marked-eigenline change of variables. -/
theorem gaussianMarkedRealDensity_log_rate
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n : ℕ => Real.log (gaussianMarkedRealDensity n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hrpos : 0 < r := by linarith
  have hcorelim := realGinibreCoreDensity_log_rate r hrpos
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ)*realGinibreCoreDensity n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
    have h := hlogn.add hcorelim
    have ht : Tendsto (fun n : ℕ =>
        Real.log ((n : ℝ)*realGinibreCoreDensity n r)/(n : ℝ))
        atTop (𝓝 (0 + -rate 1 r)) := by
      apply h.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      have hq := realGinibreCoreDensity_pos n hn r hrpos
      rw [Real.log_mul hnR.ne' hq.ne']
      ring
    simpa only [zero_add] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcorelim hupper
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hq := realGinibreCoreDensity_pos n hn r hrpos
    have hs := (gaussianMarkedRealDensity_sandwich n hn r hr.le).1
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hq hs) hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hq := realGinibreCoreDensity_pos n hn r hrpos
    have hs := (gaussianMarkedRealDensity_sandwich n hn r hr.le).2
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpoly : ((n : ℝ)+1)/2 ≤ (n : ℝ) := by linarith
    have hbound : gaussianMarkedRealDensity n r ≤
        (n : ℝ)*realGinibreCoreDensity n r :=
      hs.trans (mul_le_mul_of_nonneg_right hpoly hq.le)
    have hcand : 0 < gaussianMarkedRealDensity n r :=
      lt_of_lt_of_le hq
        (gaussianMarkedRealDensity_sandwich n hn r hr.le).1
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hcand hbound) hnR.le

#print axioms gaussianMarkedRealDensity_log_rate
end SpectralRadiusUpperTail
