import SpectralRadiusUpperTail.Rate
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The complex Ginibre rate grows at least linearly to the right of any
fixed radius above one. -/
theorem rate_two_tail_slope (r x : ℝ) (hr : 1 < r) (hrx : r ≤ x) :
    2*(r-1/r)*(x-r) ≤ rate 2 x - rate 2 r := by
  have hrpos : 0 < r := by linarith
  have hxpos : 0 < x := hrpos.trans_le hrx
  have hlog : Real.log x - Real.log r ≤ (x-r)/r := by
    rw [← Real.log_div hxpos.ne' hrpos.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hxpos hrpos)
    convert h using 1 <;> field_simp
  have hs := sq_nonneg (x-r)
  have hid : rate 2 x - rate 2 r - 2*(r-1/r)*(x-r) =
      (x-r)^2 + 2*((x-r)/r-(Real.log x-Real.log r)) := by
    unfold rate
    ring
  nlinarith

#print axioms rate_two_tail_slope
end SpectralRadiusUpperTail
