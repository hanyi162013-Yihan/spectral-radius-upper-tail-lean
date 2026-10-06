import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

theorem exponential_constant_log_rate (C I : ℝ) (hC : 0 < C) :
    Tendsto (fun n : ℕ =>
      Real.log (C * Real.exp (-(n : ℝ)*I))/(n : ℝ))
      atTop (𝓝 (-I)) := by
  have hconst : Tendsto (fun n : ℕ => Real.log C/(n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun n : ℕ => Real.log C/(n : ℝ)-I)
      atTop (𝓝 (-I)) := by simpa using hconst.sub_const I
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

#print axioms exponential_constant_log_rate
end SpectralRadiusUpperTail
