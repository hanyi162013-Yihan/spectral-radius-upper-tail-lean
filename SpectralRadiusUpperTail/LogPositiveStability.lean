import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail

lemma log_sub_le_abs_div_lower (x y m : ℝ) (hx : 0 < x) (hm : 0 < m) (hy : m ≤ y) :
    Real.log x-Real.log y ≤ |x-y|/m := by
  have hy0 := hm.trans_le hy
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hy0)
  rw [Real.log_div hx.ne' hy0.ne'] at hh
  calc
    _ ≤ x/y-1 := hh
    _ = (x-y)/y := by field_simp
    _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
    _ ≤ |x-y|/m := div_le_div_of_nonneg_left (abs_nonneg _) hm hy

lemma abs_log_sub_log_le_of_lower (x y m : ℝ) (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y|/m := by
  have h1 := log_sub_le_abs_div_lower x y m (hm.trans_le hx) hm hy
  have h2 := log_sub_le_abs_div_lower y x m (hm.trans_le hy) hm hx
  rw [abs_sub_comm y x] at h2
  exact abs_le.2 ⟨by linarith,h1⟩

#print axioms log_sub_le_abs_div_lower
#print axioms abs_log_sub_log_le_of_lower
end SpectralRadiusUpperTail
