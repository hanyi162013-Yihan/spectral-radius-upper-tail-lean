import SpectralRadiusUpperTail.MatrixRightBlockIdentity
import SpectralRadiusUpperTail.MatrixEntryOperatorBound

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma right_column_coefficient_small (A : Matrix (Fin n) (Fin n) ℂ)
    (p : Fin n → ℂ) (Q : Matrix (Fin n) ι ℂ) (r L ε : ℝ)
    (hr : 0 < r) (hε : 0 ≤ ε)
    (h : matrixIsotropicBlockControl A (fun i _ => p i) Q r ε)
    (z : ℂ) (hz : r ≤ ‖z‖) (hL : ‖z‖ ≤ L) (j : ι) :
    ‖∑ a, star (p a)*(resolvent A z*A*Q) a j‖ ≤ L*ε := by
  let P : Matrix (Fin n) ι ℂ := fun i _ => p i
  have hh := matrix_right_block_norm_le A P Q r L ε hr hε h z hz hL
  have he := (finite_matrix_entry_norm_le (Pᴴ*resolvent A z*A*Q) j j).trans hh
  have hid : (Pᴴ*resolvent A z*A*Q) j j =
      ∑ a, star (p a)*(resolvent A z*A*Q) a j := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_apply]
    rfl
  rw [hid] at he
  exact he

lemma left_frame_resolvent_coefficient_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (P : Matrix (Fin n) ι ℂ) (q : Fin n → ℂ)
    (hP : ∀ j, (∑ i, ‖P i j‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (z : ℂ) (M : ℝ) (hR : ‖resolvent A z‖ ≤ M) (j : ι) :
    ‖∑ b, (Pᴴ*resolvent A z) j b*q b‖ ≤ M := by
  have he : (∑ b, (Pᴴ*resolvent A z) j b*q b) =
      matrixCoefficient (fun i => P i j) q (resolvent A z) := by
    rw [matrixCoefficient_eq_sum]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct,
      Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  exact (matrixCoefficient_norm_le _ q (hP j) hq (resolvent A z)).trans hR

#print axioms right_column_coefficient_small
#print axioms left_frame_resolvent_coefficient_bound
end SpectralRadiusUpperTail
