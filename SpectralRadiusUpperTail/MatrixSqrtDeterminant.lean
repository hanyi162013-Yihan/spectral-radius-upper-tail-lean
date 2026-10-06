import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped MatrixOrder
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma matrix_sqrt_det_square (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef) :
    (CFC.sqrt H).det * (CFC.sqrt H).det = H.det := by
  rw [← Matrix.det_mul,CFC.sqrt_mul_sqrt_self _ hH.nonneg]

lemma matrix_sqrt_det_ne_zero (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef)
    (hd : H.det ≠ 0) : (CFC.sqrt H).det ≠ 0 := by
  intro hz
  have hh := matrix_sqrt_det_square H hH
  rw [hz,zero_mul] at hh
  exact hd hh.symm

lemma matrix_sqrt_det_norm_square (H : Matrix (Fin n) (Fin n) 𝕂) (hH : H.PosSemidef) :
    ‖(CFC.sqrt H).det‖^2 = ‖H.det‖ := by
  have hh := congrArg norm (matrix_sqrt_det_square H hH)
  simpa only [norm_mul,pow_two] using hh

lemma real_matrix_sqrt_det_abs (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef) :
    |(CFC.sqrt H).det| = Real.sqrt |H.det| := by
  have hh := matrix_sqrt_det_norm_square H hH
  simp only [Real.norm_eq_abs] at hh
  rw [← hh,Real.sqrt_sq_eq_abs,abs_abs]

#print axioms matrix_sqrt_det_square
#print axioms matrix_sqrt_det_ne_zero
#print axioms matrix_sqrt_det_norm_square
#print axioms real_matrix_sqrt_det_abs
end SpectralRadiusUpperTail
