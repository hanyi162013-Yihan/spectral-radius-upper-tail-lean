import SpectralRadiusUpperTail.HermitianSpectralJensen
import SpectralRadiusUpperTail.FrobeniusTraceIdentity
import SpectralRadiusUpperTail.ResidualGram
import Mathlib.Algebra.Order.Chebyshev

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius ComplexOrder MatrixOrder

lemma hermitian_basis_energy_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (∑ i, (inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) H (e i))).re) =
      ∑ j, hH.eigenvalues j := by
  have he (i : Fin n) := hermitian_eigenbasis_energy H hH (hH.eigenvectorBasis.repr (e i))
  simp only [LinearIsometryEquiv.symm_apply_apply] at he
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, orthonormalBasis_overlap_column, mul_one]

lemma orthonormalBasis_matrix_energy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (∑ i, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (e i)‖^2) = ‖A‖^2 := by
  simp_rw [← matrix_gram_energy]
  have he : (∑ i, RCLike.re (inner ℂ (e i)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (A.conjTranspose*A) (e i)))) =
      ∑ j, (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues j := by
    convert! hermitian_basis_energy_sum (A.conjTranspose*A)
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian e using 1
  rw [he]
  have ht := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.trace_eq_sum_eigenvalues
  have hr := congrArg RCLike.re ht
  simp only [map_sum, RCLike.ofReal_re] at hr
  rw [← hr, Matrix.trace_mul_comm, ← frobenius_norm_sq_trace]

lemma orthonormalBasis_diagonal_abs_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (∑ i, |(inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e i))).re|) ≤
      Real.sqrt (n : ℝ)*‖A‖ := by
  let d := fun i => |(inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e i))).re|
  have hd (i : Fin n) : d i ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (e i)‖ := by
    have h := (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (e i)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A (e i)))
    simpa only [e.orthonormal.1 i, one_mul, d] using h
  have hsq : (∑ i, (d i)^2) ≤ ‖A‖^2 := by
    rw [← orthonormalBasis_matrix_energy A e]
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hd i) 2)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := d)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  have hA := norm_nonneg A
  have hp : 0 ≤ Real.sqrt (n : ℝ)*‖A‖ := mul_nonneg hn0 hA
  have he : (Real.sqrt (n : ℝ)*‖A‖)^2 = (n : ℝ)*‖A‖^2 := by rw [mul_pow, hn]
  change (∑ i, d i) ≤ _
  nlinarith

#print axioms hermitian_basis_energy_sum
#print axioms orthonormalBasis_matrix_energy
#print axioms orthonormalBasis_diagonal_abs_sum
end SpectralRadiusUpperTail
