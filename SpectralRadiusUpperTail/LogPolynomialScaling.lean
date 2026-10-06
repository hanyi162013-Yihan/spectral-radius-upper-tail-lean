import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- Positive constant factors and fixed powers of `n` do not change a
speed-`n` logarithmic rate. -/
theorem log_polynomial_scaling_rate (q : ℕ → ℝ) (L c : ℝ)
    (p : ℕ) (hc : 0 < c)
    (hq : ∀ᶠ n in atTop, 0 < q n)
    (hlim : Tendsto (fun n : ℕ => Real.log (q n)/(n : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ =>
      Real.log (c*q n/(n : ℝ)^p)/(n : ℝ)) atTop (𝓝 L) := by
  have hconst : Tendsto (fun n : ℕ => Real.log c/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hpoly : Tendsto (fun n : ℕ =>
      (p : ℝ)*(Real.log (n : ℝ)/(n : ℝ))) atTop (𝓝 0) := by
    simpa using hlogn.const_mul (p : ℝ)
  have hsum := (hconst.add hlim).sub hpoly
  have hsum' : Tendsto (fun n : ℕ =>
      Real.log c/(n : ℝ)+Real.log (q n)/(n : ℝ)-
        (p : ℝ)*(Real.log (n : ℝ)/(n : ℝ))) atTop (𝓝 L) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [hq, eventually_gt_atTop 0] with n hqn hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_div (mul_ne_zero hc.ne' hqn.ne') (pow_ne_zero _ hnR.ne'),
    Real.log_mul hc.ne' hqn.ne', Real.log_pow]
  ring

#print axioms log_polynomial_scaling_rate
end SpectralRadiusUpperTail
