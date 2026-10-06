import SpectralRadiusUpperTail.FrobeniusTraceIdentity
import Mathlib.Analysis.Matrix.Spectrum

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix Matrix.Norms.L2Operator
variable {n : ℕ}

lemma matrix_diagonal_mask_norm_le (d : Fin n → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hd : ∀ i, ‖d i‖ ≤ a) : ‖(Matrix.diagonal d : Matrix (Fin n) (Fin n) ℂ)‖ ≤ a := by
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg ha).mpr hd

lemma masked_gram_identity (B : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hB : Bᴴ*B = Matrix.diagonal (fun i => (lam i : ℂ))) (d : Fin n → ℝ) :
    (B*Matrix.diagonal (fun i => (d i : ℂ)))ᴴ *
      (B*Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (((d i)^2*lam i : ℝ) : ℂ)) := by
  rw [Matrix.conjTranspose_mul]
  have hd : (Matrix.diagonal (fun i => (d i : ℂ)))ᴴ = Matrix.diagonal (fun i => (d i : ℂ)) := by
    simp
  rw [hd]
  calc
    _ = Matrix.diagonal (fun i => (d i : ℂ)) * (Bᴴ*B) * Matrix.diagonal (fun i => (d i : ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hB,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      push_cast
      ring

lemma masked_matrix_norm_le (B : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ)
    (hB : Bᴴ*B = Matrix.diagonal (fun i => (lam i : ℂ))) (d : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hlam : ∀ i, 0 ≤ lam i) (hd : ∀ i, (d i)^2*lam i ≤ δ^2) :
    ‖B*Matrix.diagonal (fun i => (d i : ℂ))‖ ≤ δ := by
  have hh := matrix_diagonal_mask_norm_le (fun i => (((d i)^2*lam i : ℝ) : ℂ))
    (δ^2) (sq_nonneg δ) (fun i => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (hlam i))]
      exact hd i)
  rw [← masked_gram_identity B lam hB d,Matrix.l2_opNorm_conjTranspose_mul_self] at hh
  nlinarith [norm_nonneg (B*Matrix.diagonal (fun i => (d i : ℂ)))]

#print axioms matrix_diagonal_mask_norm_le
#print axioms masked_gram_identity
#print axioms masked_matrix_norm_le
end SpectralRadiusUpperTail
