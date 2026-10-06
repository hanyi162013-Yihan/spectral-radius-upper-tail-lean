import SpectralRadiusUpperTail.MarkedRealNoSpectrumFubini
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The absolute Jacobian determinant is the absolute characteristic
polynomial of the complementary matrix evaluated at the marked scalar. -/
theorem markedReal_abs_det_sub_scalar_eq_charpoly
    (m : ℕ) (H : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) :
    |(H - x • (1 : Matrix (Fin m) (Fin m) ℝ)).det| =
      |H.charpoly.eval x| := by
  have hmat : H - x • (1 : Matrix (Fin m) (Fin m) ℝ) =
      -(Matrix.scalar (Fin m) x - H) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.one_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> ring
  rw [hmat, Matrix.det_neg]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← Matrix.eval_charpoly H x]

#print axioms markedReal_abs_det_sub_scalar_eq_charpoly
end SpectralRadiusUpperTail
