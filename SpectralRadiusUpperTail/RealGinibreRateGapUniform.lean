import SpectralRadiusUpperTail.Rate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The extra factor of `r` in comparing the finite-Poisson term with the
dominant real-Ginibre term costs only a universal constant. -/
theorem realGinibre_log_sub_rate_uniform (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) :
    Real.log r - (n : ℝ)*rate 1 r ≤ (1/2 : ℝ) := by
  have hrpos : 0 < r := by linarith
  have hq : 0 < r^2/2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div (pow_ne_zero _ hrpos.ne')
    (by norm_num : (2 : ℝ) ≠ 0), Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hrate : 0 ≤ rate 1 r := rate_nonneg 1 r (by norm_num) hrpos
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmore := mul_nonneg (sub_nonneg.mpr hnR) hrate
  unfold rate at hrate hmore ⊢
  nlinarith

#print axioms realGinibre_log_sub_rate_uniform
end SpectralRadiusUpperTail
