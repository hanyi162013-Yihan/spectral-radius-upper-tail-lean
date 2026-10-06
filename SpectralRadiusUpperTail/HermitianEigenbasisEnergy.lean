import SpectralRadiusUpperTail.MatrixSqrtEnergy
import Mathlib.Analysis.Matrix.Spectrum

namespace SpectralRadiusUpperTail
open scoped BigOperators ComplexOrder MatrixOrder

lemma hermitian_eigenbasis_action {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (v : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis.repr.symm v) =
      hH.eigenvectorBasis.repr.symm
        (WithLp.toLp 2 (fun i => (hH.eigenvalues i : ℂ)*v i)) := by
  have hb (i : Fin n) : Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis i) =
      (hH.eigenvalues i : ℂ) • hH.eigenvectorBasis i := by
    apply WithLp.ofLp_injective 2
    have he := hH.mulVec_eigenvectorBasis i
    funext j
    have hj := congrFun he j
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, Pi.smul_apply,
      RCLike.real_smul_eq_coe_mul, smul_eq_mul] using! hj
  rw [← hH.eigenvectorBasis.sum_repr_symm v, map_sum,
    ← hH.eigenvectorBasis.sum_repr_symm]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hb, smul_smul]
  simp only [WithLp.ofLp_toLp]
  rw [mul_comm]

lemma hermitian_eigenbasis_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (hH.eigenvectorBasis.repr.symm v)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis.repr.symm v))).re =
        ∑ i, hH.eigenvalues i*‖v i‖^2 := by
  rw [hermitian_eigenbasis_action, LinearIsometryEquiv.inner_map_map]
  rw [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [WithLp.ofLp_toLp, RCLike.inner_apply, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

#print axioms hermitian_eigenbasis_action
#print axioms hermitian_eigenbasis_energy
end SpectralRadiusUpperTail
