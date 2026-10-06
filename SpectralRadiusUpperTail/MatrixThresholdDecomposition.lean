import SpectralRadiusUpperTail.ThresholdEigenvalueCount
import Mathlib.LinearAlgebra.Matrix.Rank

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma unitary_diagonal_split (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (1 : ℂ) else 0)*
      (star U : Matrix (Fin n) (Fin n) ℂ) +
    D*(U : Matrix (Fin n) (Fin n) ℂ)*Matrix.diagonal (fun i => if i ∈ s then (0 : ℂ) else 1)*
      (star U : Matrix (Fin n) (Fin n) ℂ) = D := by
  classical
  rw [← Matrix.add_mul,← Matrix.mul_add,Matrix.diagonal_add]
  have hd : (fun i => (if i ∈ s then (1 : ℂ) else 0) +
      (if i ∈ s then (0 : ℂ) else 1)) = fun _ => 1 := by
    funext i
    split_ifs <;> simp
  rw [hd,Matrix.diagonal_one,Matrix.mul_one,Matrix.mul_assoc,← Unitary.coe_star,Unitary.coe_mul_star_self,
    Matrix.mul_one]

lemma threshold_remainder_norm_le (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hD : (D*(U : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (D*(U : Matrix (Fin n) (Fin n) ℂ)) = Matrix.diagonal (fun i => (lam i : ℂ)))
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖D*(U : Matrix (Fin n) (Fin n) ℂ)*
      Matrix.diagonal (fun i => if i ∈ eigenvalueActiveSet lam δ then (0 : ℂ) else 1)*
      (star U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ δ := by
  classical
  rw [← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
  have hh := masked_matrix_norm_le (D*(U : Matrix (Fin n) (Fin n) ℂ)) lam hD
    (fun i => if i ∈ eigenvalueActiveSet lam δ then (0 : ℝ) else 1) δ hδ hlam (by
      intro i
      split_ifs with hi
      · simpa using sq_nonneg δ
      · have hi' : lam i ≤ δ^2 := by
          simpa [eigenvalueActiveSet] using hi
        simpa using hi')
  simpa only [apply_ite,Complex.ofReal_zero,Complex.ofReal_one] using hh

lemma matrix_norm_le_of_HSsq (D : Matrix (Fin n) (Fin n) ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hD : matrixHSsq D ≤ C^2) : ‖D‖ ≤ C := by
  obtain ⟨U,lam,hlam,hgram,hsum⟩ := matrix_gram_eigenbasis D
  have hh := masked_matrix_norm_le (D*(U : Matrix (Fin n) (Fin n) ℂ)) lam hgram
    (fun _ => 1) C hC hlam (fun i => by
      simpa only [one_pow,one_mul] using (eigenvalue_le_sum lam hlam i).trans (hsum ▸ hD))
  simpa only [Complex.ofReal_one,Matrix.diagonal_one,Matrix.mul_one,
    CStarRing.norm_mul_coe_unitary] using hh

#print axioms unitary_diagonal_split
#print axioms threshold_remainder_norm_le
#print axioms matrix_norm_le_of_HSsq
end SpectralRadiusUpperTail
