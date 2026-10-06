import SpectralRadiusUpperTail.MatrixCoefficientBlock
import SpectralRadiusUpperTail.MatrixEntryOperatorBound

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rectangular_coefficient_expansion (p q : Fin n → ℂ)
    (L : Matrix (Fin n) ι ℂ) (S : Matrix ι ι ℂ) (V : Matrix ι (Fin n) ℂ) :
    matrixCoefficient p q (L*S*V) =
      ∑ i, ∑ j, (∑ a, star (p a)*L a i)*S i j*(∑ b, V j b*q b) := by
  let P : Matrix (Fin n) (Fin 1) ℂ := fun a _ => p a
  let Q : Matrix (Fin n) (Fin 1) ℂ := fun b _ => q b
  have hh := matrixCoefficient_block_entry P Q (L*S*V) 0 0
  change (Pᴴ*(L*S*V)*Q) 0 0 = matrixCoefficient p q (L*S*V) at hh
  rw [← hh]
  have he : Pᴴ*(L*S*V)*Q = (Pᴴ*L)*S*(V*Q) := by simp only [Matrix.mul_assoc]
  rw [he]
  have hPl (i : ι) : (Pᴴ*L) 0 i = ∑ a, star (p a)*L a i := by
    rw [Matrix.mul_apply]
    rfl
  have hVq (j : ι) : (V*Q) j 0 = ∑ b, V j b*q b := by
    rw [Matrix.mul_apply]
  have hLS (j : ι) : (Pᴴ*L*S) 0 j = ∑ i, (∑ a, star (p a)*L a i)*S i j := by
    rw [Matrix.mul_apply]
    simp only [hPl]
  rw [Matrix.mul_apply]
  simp only [hLS,hVq,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma rectangular_coefficient_bound (p q : Fin n → ℂ)
    (L : Matrix (Fin n) ι ℂ) (S : Matrix ι ι ℂ) (V : Matrix ι (Fin n) ℂ)
    (ε M : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hleft : ∀ i, ‖∑ a, star (p a)*L a i‖ ≤ ε)
    (hS : ‖S‖ ≤ 2) (hright : ∀ j, ‖∑ b, V j b*q b‖ ≤ M) :
    ‖matrixCoefficient p q (L*S*V)‖ ≤ (Fintype.card ι : ℝ)^2*(2*ε*M) := by
  rw [rectangular_coefficient_expansion]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, ∑ _j : ι, 2*ε*M := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul]
      have he := (finite_matrix_entry_norm_le S i j).trans hS
      have hh := mul_le_mul (hleft i) he (norm_nonneg _) hε
      have ht := mul_le_mul hh (hright j) (norm_nonneg _) (by positivity : 0 ≤ ε*2)
      exact ht.trans_eq (by ring)
    _ = _ := by simp; ring

#print axioms rectangular_coefficient_expansion
#print axioms rectangular_coefficient_bound
end SpectralRadiusUpperTail
