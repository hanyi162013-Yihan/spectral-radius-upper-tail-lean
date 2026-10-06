import SpectralRadiusUpperTail.RealSchurBlockPower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The scalar-versus-conjugate-pair Sylvester factor in the real Schur
Jacobian. It is the real determinant of the two-dimensional block
`B-aI`, and equals the product of the two complex spectral gaps. -/
theorem realSchur_scalar_pair_factor (a x b c y : ℝ)
    (hbc : b*c = y^2) :
    Matrix.det (realSchurBlock x b c - Matrix.scalar (Fin 2) a) =
      ‖((x-a : ℝ) : ℂ)+y*Complex.I‖^2 := by
  have hdet : Matrix.det (realSchurBlock x b c -
      Matrix.scalar (Fin 2) a) = (x-a)^2+b*c := by
    simp [realSchurBlock, Matrix.det_fin_two, Matrix.sub_apply,
      Matrix.scalar]
    ring
  rw [hdet, hbc, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  ring

theorem realSchur_scalar_pair_factor_pos (a x b c y : ℝ)
    (hbc : b*c = y^2) (hy : y ≠ 0) :
    0 < Matrix.det (realSchurBlock x b c - Matrix.scalar (Fin 2) a) := by
  rw [realSchur_scalar_pair_factor a x b c y hbc]
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hvalue : ‖((x-a : ℝ) : ℂ)+y*Complex.I‖^2 =
      (x-a)^2+y^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [hvalue]
  nlinarith [sq_nonneg (x-a)]

#print axioms realSchur_scalar_pair_factor
#print axioms realSchur_scalar_pair_factor_pos
end SpectralRadiusUpperTail
