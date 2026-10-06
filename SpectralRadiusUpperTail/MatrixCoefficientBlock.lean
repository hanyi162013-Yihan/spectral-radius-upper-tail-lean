import SpectralRadiusUpperTail.MatrixCoefficientDifference
import SpectralRadiusUpperTail.FiniteMatrixEntryBound

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixCoefficient_block_entry (P Q : Matrix (Fin n) ι ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    (Pᴴ*A*Q) i j = matrixCoefficient (fun k => P k i) (fun k => Q k j) A := by
  rw [Matrix.mul_assoc,matrixCoefficient_eq_sum]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct]

lemma matrixCoefficient_block_error (P Q : Matrix (Fin n) ι ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (i j : ι) :
    (Pᴴ*A*Q-s • (Pᴴ*Q)) i j =
      matrixCoefficient (fun k => P k i) (fun k => Q k j) A -
        s*matrixCoefficient (fun k => P k i) (fun k => Q k j) 1 := by
  rw [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,matrixCoefficient_block_entry]
  have hh := matrixCoefficient_block_entry P Q 1 i j
  rw [Matrix.mul_one] at hh
  rw [hh]

lemma matrixCoefficient_block_norm_le (P Q : Matrix (Fin n) ι ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖matrixCoefficient (fun k => P k i) (fun k => Q k j) A -
        s*matrixCoefficient (fun k => P k i) (fun k => Q k j) 1‖ ≤ δ) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Pᴴ*A*Q-s • (Pᴴ*Q))‖ ≤
      (Fintype.card ι : ℝ)*δ := by
  apply finite_matrix_operator_entry_bound _ δ hδ
  intro i j
  rw [matrixCoefficient_block_error]
  exact h i j

#print axioms matrixCoefficient_block_entry
#print axioms matrixCoefficient_block_error
#print axioms matrixCoefficient_block_norm_le
end SpectralRadiusUpperTail
