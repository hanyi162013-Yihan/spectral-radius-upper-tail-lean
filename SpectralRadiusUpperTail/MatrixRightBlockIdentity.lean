import SpectralRadiusUpperTail.ResolventRightProduct
import SpectralRadiusUpperTail.IsotropicBlockControl

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_right_block_identity (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (z : ℂ) (hz0 : z ≠ 0)
    (hz : z ∈ resolventSet ℂ A) :
    Pᴴ*resolvent A z*A*Q = z • (Pᴴ*resolvent A z*Q-z⁻¹ • (Pᴴ*Q)) := by
  calc
    _ = Pᴴ*(resolvent A z*A)*Q := by simp only [Matrix.mul_assoc]
    _ = (z • (Pᴴ*resolvent A z)-Pᴴ)*Q := by
      rw [resolvent_mul_element A z hz,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one]
    _ = z • (Pᴴ*resolvent A z*Q)-Pᴴ*Q := by rw [Matrix.sub_mul,Matrix.smul_mul]
    _ = _ := by rw [smul_sub,smul_smul,mul_inv_cancel₀ hz0,one_smul]

lemma matrix_right_block_norm_le (A : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Matrix (Fin n) ι ℂ) (r L ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (h : matrixIsotropicBlockControl A P Q r ε)
    (z : ℂ) (hz : r ≤ ‖z‖) (hL : ‖z‖ ≤ L) :
    ‖Pᴴ*resolvent A z*A*Q‖ ≤ L*ε := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hz)
  rw [matrix_right_block_identity A P Q z hz0 (h z hz).1,norm_smul]
  have he : ‖Pᴴ*resolvent A z*Q-z⁻¹ • (Pᴴ*Q)‖ ≤ ε := (h z hz).2.le
  exact mul_le_mul hL he (norm_nonneg _) (le_trans (norm_nonneg z) hL)

#print axioms matrix_right_block_identity
#print axioms matrix_right_block_norm_le
end SpectralRadiusUpperTail
