import SpectralRadiusUpperTail.AlgebraPowerDifference
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A real Schur block with conjugate eigenvalues x ± iy, where bc=y^2. -/
def realSchurBlock (x b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x, b; -c, x]

lemma real_schur_block_power_formula (x b c y : ℝ) (hy : y ≠ 0)
    (hbc : b*c = y^2) (k : ℕ) :
    (realSchurBlock x b c)^k =
      !![(((x : ℂ)+y*Complex.I)^k).re, (b/y)*(((x : ℂ)+y*Complex.I)^k).im;
        -(c/y)*(((x : ℂ)+y*Complex.I)^k).im, (((x : ℂ)+y*Complex.I)^k).re] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [realSchurBlock]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realSchurBlock, Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      field_simp [hy] <;>
      nlinarith [hbc, congrArg (fun t : ℝ => t*(((x : ℂ)+y*Complex.I)^k).im) hbc]

/-- The imaginary coefficient of a complex power is controlled by a
power-difference estimate against its conjugate. -/
lemma complex_power_im_le (z : ℂ) (k : ℕ) :
    |(z^(k+1)).im| ≤ ((k+1 : ℕ) : ℝ)*‖z‖^k*|z.im| := by
  have hh := algebra_power_difference_le z (star z) (norm_nonneg z) le_rfl
    (by simp) k
  have he (w : ℂ) : ‖w-star w‖ = 2*|w.im| := by
    have hw : w-star w = (2*w.im : ℝ)*Complex.I := by
      apply Complex.ext <;> simp <;> ring
    rw [hw, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← star_pow, he, he] at hh
  nlinarith

#print axioms real_schur_block_power_formula
#print axioms complex_power_im_le
end SpectralRadiusUpperTail
