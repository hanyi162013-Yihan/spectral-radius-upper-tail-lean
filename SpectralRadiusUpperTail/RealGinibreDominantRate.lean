import SpectralRadiusUpperTail.RealGinibreDominantDensity
import Mathlib.Topology.Order.Basic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The dominant real one-point term alone has the sharp speed-`n` rate.
The exact real-eigenvalue one-point formula and tail integration are still
separate steps. -/
theorem realGinibreDominantDensity_log_rate (r : ℝ) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => Real.log (realGinibreDominantDensity n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hrpos : 0 < r := by linarith
  have hcore := realGinibreCoreDensity_log_rate r hrpos
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlowlim : Tendsto (fun n : ℕ =>
      Real.log (realGinibreCoreDensity n r)/(n : ℝ) -
        Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 (-rate 1 r)) := by
    simpa using hcore.sub hlogn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hcore
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hcorepos := realGinibreCoreDensity_pos n hnpos r hrpos
    have hb := (realGinibreDominantDensity_bounds n hn r hr).1
    have hlog := Real.log_le_log (div_pos hcorepos hnR) hb
    rw [Real.log_div hcorepos.ne' hnR.ne'] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog hnR.le
    calc
      Real.log (realGinibreCoreDensity n r)/(n : ℝ) -
          Real.log (n : ℝ)/(n : ℝ) =
          (Real.log (realGinibreCoreDensity n r)-Real.log (n : ℝ))/(n : ℝ) := by ring
      _ ≤ _ := hdiv
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hcorepos := realGinibreCoreDensity_pos n hnpos r hrpos
    have hb := realGinibreDominantDensity_bounds n hn r hr
    have hdompos : 0 < realGinibreDominantDensity n r :=
      lt_of_lt_of_le (div_pos hcorepos hnR) hb.1
    have hlog := Real.log_le_log hdompos hb.2
    exact div_le_div_of_nonneg_right hlog hnR.le

#print axioms realGinibreDominantDensity_log_rate
end SpectralRadiusUpperTail
