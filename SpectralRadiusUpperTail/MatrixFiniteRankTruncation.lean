import SpectralRadiusUpperTail.MatrixThresholdDecomposition

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma diagonal_indicator_rank (s : Finset (Fin n)) :
    (Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)).rank = s.card := by
  classical
  rw [Matrix.rank_diagonal]
  let e : {i : Fin n // (if i ∈ s then (1 : ℂ) else 0) ≠ 0} ≃ s :=
    Equiv.subtypeEquivRight (fun i => by simp)
  exact (Fintype.card_congr e).trans (Fintype.card_coe s)

lemma unitary_mask_rank_le (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    (D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ)).rank ≤ s.card := by
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans_eq (diagonal_indicator_rank s))

lemma unitary_mask_norm_le (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    ‖D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ ‖D‖ := by
  classical
  rw [← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
  have hd : ‖(Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0) :
      Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := matrix_diagonal_mask_norm_le _ 1 (by norm_num) (by
        intro i
        split_ifs <;> simp)
  apply (norm_mul_le _ _).trans
  rw [CStarRing.norm_mul_coe_unitary]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (norm_nonneg D)

/-- Explicit Euclidean operator remainder bound and dimension-free rank budget.
The Hilbert--Schmidt quantity is the sum of squared entry norms. -/
lemma matrix_HS_finite_rank_truncation (D : Matrix (Fin n) (Fin n) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ H E : Matrix (Fin n) (Fin n) ℂ,
      H+E = D ∧ ‖E‖ ≤ δ ∧ ‖H‖ ≤ ‖D‖ ∧ (H.rank : ℝ)*δ^2 ≤ matrixHSsq D := by
  classical
  obtain ⟨U,lam,hlam,hgram,hsum⟩ := matrix_gram_eigenbasis D
  let s := eigenvalueActiveSet lam δ
  refine ⟨D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then 1 else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ),
    D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then 0 else 1)*
      (star U : Matrix (Fin n) (Fin n) ℂ),
    unitary_diagonal_split D U s,threshold_remainder_norm_le D U lam hlam hgram δ hδ,
    unitary_mask_norm_le D U s,?_⟩
  have hr : (((D*(U : Matrix (Fin n) (Fin n) ℂ)*
      Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ)).rank : ℕ) : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast unitary_mask_rank_le D U s
  exact (mul_le_mul_of_nonneg_right hr (sq_nonneg δ)).trans
    ((eigenvalue_active_count lam hlam δ).trans_eq hsum)

#print axioms diagonal_indicator_rank
#print axioms unitary_mask_rank_le
#print axioms unitary_mask_norm_le
#print axioms matrix_HS_finite_rank_truncation
end SpectralRadiusUpperTail
