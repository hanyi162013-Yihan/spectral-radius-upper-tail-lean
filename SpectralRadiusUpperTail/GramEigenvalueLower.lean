import SpectralRadiusUpperTail.ResidualGram
import Mathlib.Analysis.Matrix.Spectrum

namespace SpectralRadiusUpperTail
open scoped ComplexOrder MatrixOrder

lemma gram_eigenvalue_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i =
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A
        ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis i)‖^2 := by
  rw [← matrix_gram_energy]
  have he := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues_eq i
  convert! he using 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  rfl

lemma gram_eigenvalues_inverse_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hSA : ∀ v, S (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) = v)
    (M : ℝ) (hM : 0 < M) (hS : ‖S‖ ≤ M) (i : Fin n) :
    0 < (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i ∧
      ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)⁻¹ ≤ M^2 := by
  let v := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis i
  have hv : ‖v‖ = 1 := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis.orthonormal.1 i
  have hbound := (S.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) A v)).trans
    (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  rw [hSA, hv] at hbound
  have he := gram_eigenvalue_energy A i
  have hsq : 1 ≤ M^2*(Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
    rw [he]
    have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hbound
    dsimp [v] at hs
    nlinarith
  have hpos : 0 < (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i := by
    nlinarith [sq_nonneg M]
  refine ⟨hpos, ?_⟩
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hpos).mpr hsq

#print axioms gram_eigenvalue_energy
#print axioms gram_eigenvalues_inverse_bound
end SpectralRadiusUpperTail
