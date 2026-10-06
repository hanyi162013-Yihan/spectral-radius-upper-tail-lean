import SpectralRadiusUpperTail.RealGinibreGammaRate
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The positive factor in the real-eigenvalue one-point formula after
normalizing its incomplete Gamma integral to a probability. -/
noncomputable def realGinibreCoreDensity (n : ℕ) (r : ℝ) : ℝ :=
  (((n : ℝ)/2)^((n : ℝ)/2) * r^((n : ℝ)-1) *
    Real.exp (-(n : ℝ)*r^2/2)) / Real.Gamma ((n : ℝ)/2)

theorem realGinibreCoreDensity_pos (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) : 0 < realGinibreCoreDensity n r := by
  unfold realGinibreCoreDensity
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

/-- The logarithmic form separates the exact Gamma normalization from
the location-dependent Gaussian exponential. -/
theorem realGinibreCoreDensity_log (n : ℕ) (hn : 0 < n)
    (r : ℝ) (hr : 0 < r) :
    Real.log (realGinibreCoreDensity n r)/(n : ℝ) =
      realGinibreGammaLogCore n r + Real.log ((n : ℝ)/2)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnh : (0 : ℝ) < (n : ℝ)/2 := by positivity
  have hG : 0 < Real.Gamma ((n : ℝ)/2) := Real.Gamma_pos_of_pos hnh
  have hGp : Real.Gamma ((n : ℝ)/2+1) =
      ((n : ℝ)/2)*Real.Gamma ((n : ℝ)/2) :=
    Real.Gamma_add_one hnh.ne'
  have hlog : Real.log (Real.Gamma ((n : ℝ)/2+1)) =
      Real.log ((n : ℝ)/2)+Real.log (Real.Gamma ((n : ℝ)/2)) := by
    rw [hGp, Real.log_mul hnh.ne' hG.ne']
  unfold realGinibreCoreDensity realGinibreGammaLogCore
  rw [Real.log_div (by positivity) hG.ne',
    Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hr _).ne',
    Real.log_rpow hnh, Real.log_rpow hr, Real.log_exp]
  rw [hlog]
  field_simp
  ring

theorem realGinibreCoreDensity_log_rate (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ => Real.log (realGinibreCoreDensity n r)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hlogn : Tendsto (fun n : ℕ => Real.log ((n : ℝ)/2)/(n : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ))
        atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := h1.sub h2
    have h' : Tendsto (fun n : ℕ =>
        Real.log (n : ℝ)/(n : ℝ)-Real.log 2/(n : ℝ)) atTop (𝓝 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [Real.log_div hnR.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have ht := (realGinibreGammaLogCore_limit r hr).add hlogn
  have ht' : Tendsto (fun n : ℕ =>
      realGinibreGammaLogCore n r + Real.log ((n : ℝ)/2)/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (realGinibreCoreDensity_log n hn r hr).symm

#print axioms realGinibreCoreDensity_log
#print axioms realGinibreCoreDensity_log_rate
end SpectralRadiusUpperTail
