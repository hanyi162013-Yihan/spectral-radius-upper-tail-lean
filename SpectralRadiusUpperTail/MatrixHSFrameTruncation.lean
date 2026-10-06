import SpectralRadiusUpperTail.MatrixFiniteRankTruncation
import SpectralRadiusUpperTail.UnitaryFrameProjection

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A concrete column factorization of the finite-rank approximation. All matrix
norms here are Euclidean operator norms; matrixHSsq is explicitly entrywise. -/
lemma matrix_HS_frame_truncation (D : Matrix (Fin n) (Fin n) ℂ)
    (C δ : ℝ) (hC : 0 ≤ C) (hHS : matrixHSsq D ≤ C^2) (hδ : 0 ≤ δ) :
    ∃ s : Finset (Fin n), ∃ W : Matrix (Fin n) s ℂ,
      Wᴴ*W = 1 ∧ ‖W‖ ≤ 1 ∧ ‖D*W‖ ≤ C ∧
        ‖D-D*W*Wᴴ‖ ≤ δ ∧ (s.card : ℝ)*δ^2 ≤ C^2 := by
  classical
  obtain ⟨U,lam,hlam,hgram,hsum⟩ := matrix_gram_eigenbasis D
  let s := eigenvalueActiveSet lam δ
  let e : s ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  let W := (U : Matrix (Fin n) (Fin n) ℂ).submatrix id e
  have hW : ‖W‖ ≤ 1 := unitary_column_frame_norm_le U e
  refine ⟨s,W,unitary_column_frame_gram U e,hW,?_,?_,?_⟩
  · have hh := Matrix.l2_opNorm_mul D W
    have hD := matrix_norm_le_of_HSsq D C hC hHS
    exact hh.trans (by nlinarith [norm_nonneg D,norm_nonneg W])
  · have hsplit := unitary_diagonal_split D U s
    have he := threshold_remainder_norm_le D U lam hlam hgram δ hδ
    have hfactor := unitary_frame_factorization D U s
    change D*W*Wᴴ = _ at hfactor
    rw [← hfactor] at hsplit
    have hh : D-D*W*Wᴴ = D*(U : Matrix (Fin n) (Fin n) ℂ)*
        Matrix.diagonal (fun i => if i ∈ s then (0 : ℂ) else 1)*
        (star U : Matrix (Fin n) (Fin n) ℂ) := by
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using hsplit.symm
    rw [hh]
    exact he
  · exact (eigenvalue_active_count lam hlam δ).trans (hsum ▸ hHS)

lemma truncation_card_bound (s : Finset (Fin n)) (C δ : ℝ) (hδ : 0 < δ)
    (h : (s.card : ℝ)*δ^2 ≤ C^2) : s.card ≤ ⌈C^2/δ^2⌉₊ := by
  have hh : (s.card : ℝ) ≤ C^2/δ^2 := (le_div_iff₀ (sq_pos_of_pos hδ)).mpr h
  exact_mod_cast hh.trans (Nat.le_ceil (C^2/δ^2))

#print axioms matrix_HS_frame_truncation
#print axioms truncation_card_bound
end SpectralRadiusUpperTail
