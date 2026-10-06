import SpectralRadiusUpperTail.Rate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The linear-power rate is nonnegative at unit variance. -/
theorem powerRate_one_nonneg (α : ℝ) (hα : 0 ≤ α) :
    0 ≤ powerRate 1 α := by
  have hx : 0 < 1+2*α := by linarith
  have h := entropy_gap_nonneg (1+2*α) 1 hx (by norm_num)
  simp only [div_one, Real.log_one, add_zero] at h
  unfold powerRate
  norm_num
  nlinarith

#print axioms powerRate_one_nonneg
end SpectralRadiusUpperTail
