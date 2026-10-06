import SpectralRadiusUpperTail.MatrixMaskGram
import Mathlib.Analysis.Matrix.PosDef

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix ComplexOrder
variable {n : ℕ}

noncomputable def matrixHSsq (D : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖D i j‖^2

lemma matrixHSsq_eq_trace (D : Matrix (Fin n) (Fin n) ℂ) :
    matrixHSsq D = Complex.re (Dᴴ*D).trace := by
  rw [Matrix.trace_mul_comm]
  simp only [matrixHSsq,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,Complex.ofReal_re]

lemma hermitian_eigenbasis_diagonal (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ*A*
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  have hh := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hh
  exact hh

lemma hermitian_trace_real (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    Complex.re A.trace = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues,Complex.re_sum]
  rfl

lemma gram_after_unitary (D : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (D*(U : Matrix (Fin n) (Fin n) ℂ))ᴴ*(D*(U : Matrix (Fin n) (Fin n) ℂ)) =
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ*(Dᴴ*D)*(U : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma matrix_gram_eigenbasis (D : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ lam : Fin n → ℝ,
      (∀ i, 0 ≤ lam i) ∧
      (D*(U : Matrix (Fin n) (Fin n) ℂ))ᴴ * (D*(U : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.diagonal (fun i => (lam i : ℂ)) ∧ (∑ i, lam i) = matrixHSsq D := by
  let hH := Matrix.isHermitian_conjTranspose_mul_self D
  refine ⟨hH.eigenvectorUnitary,hH.eigenvalues,
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg D,?_,?_⟩
  · rw [gram_after_unitary]
    exact hermitian_eigenbasis_diagonal (Dᴴ*D) hH
  · rw [matrixHSsq_eq_trace]
    exact (hermitian_trace_real (Dᴴ*D) hH).symm

#print axioms hermitian_eigenbasis_diagonal
#print axioms hermitian_trace_real
#print axioms gram_after_unitary
#print axioms matrixHSsq
#print axioms matrixHSsq_eq_trace
#print axioms matrix_gram_eigenbasis
end SpectralRadiusUpperTail
