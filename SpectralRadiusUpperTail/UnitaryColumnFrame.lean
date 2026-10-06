import SpectralRadiusUpperTail.MatrixMaskGram

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_column_frame_gram (U : Matrix.unitaryGroup (Fin n) ℂ)
    (e : ι ↪ Fin n) :
    ((U : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ *
      ((U : Matrix (Fin n) (Fin n) ℂ).submatrix id e) = 1 := by
  have hh := Matrix.submatrix_mul (star (U : Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ) e id e Function.bijective_id
  rw [Unitary.coe_star_mul_self] at hh
  simp only [Matrix.star_eq_conjTranspose] at hh
  rw [Matrix.conjTranspose_submatrix]
  rw [← hh]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff]

lemma unitary_column_frame_norm_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (e : ι ↪ Fin n) :
    ‖(U : Matrix (Fin n) (Fin n) ℂ).submatrix id e‖ ≤ 1 := by
  have hgram := unitary_column_frame_gram U e
  have hn : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr (by simp)
  rw [← hgram,Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg ((U : Matrix (Fin n) (Fin n) ℂ).submatrix id e)]

#print axioms unitary_column_frame_gram
#print axioms unitary_column_frame_norm_le
end SpectralRadiusUpperTail
