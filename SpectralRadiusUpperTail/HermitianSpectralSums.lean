import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma hermitian_spectral_sum_roots (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (hH.eigenvalues i)) = (H.charpoly.roots.map (fun z : ℂ => f z.re)).sum := by
  rw [hH.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_map, Function.comp_def]

lemma hermitian_spectral_sum_charpoly (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) (he : H.charpoly = K.charpoly) (f : ℝ → ℝ) :
    (∑ i, f (hH.eigenvalues i)) = ∑ j, f (hK.eigenvalues j) := by
  rw [hermitian_spectral_sum_roots H hH f, hermitian_spectral_sum_roots K hK f, he]

lemma hermitian_spectral_sum_cfc (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (f g : ℝ → ℝ) (hF : (cfc f H).IsHermitian) :
    (∑ i, g (hF.eigenvalues i)) = ∑ i, g (f (hH.eigenvalues i)) := by
  rw [hermitian_spectral_sum_roots _ hF g, hH.charpoly_cfc_eq]
  rw [Polynomial.roots_prod]
  · simp [Multiset.map_map, Function.comp_def]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

lemma hermitian_spectral_sum_blocks (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hB : (Matrix.fromBlocks H 0 0 K).IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (hB.eigenvalues i)) = (∑ i, f (hH.eigenvalues i))+(∑ i, f (hK.eigenvalues i)) := by
  rw [hermitian_spectral_sum_roots _ hB f, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic H).ne_zero (Matrix.charpoly_monic K).ne_zero),
    Multiset.map_add, Multiset.sum_add]
  rw [← hermitian_spectral_sum_roots H hH f, ← hermitian_spectral_sum_roots K hK f]

#print axioms hermitian_spectral_sum_roots
#print axioms hermitian_spectral_sum_charpoly
#print axioms hermitian_spectral_sum_cfc
#print axioms hermitian_spectral_sum_blocks
end SpectralRadiusUpperTail
