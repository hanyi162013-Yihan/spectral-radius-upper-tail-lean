import SpectralRadiusUpperTail.HermitianSpectralJensen

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma hermitian_eigenvector_energy {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (i : Fin n) :
    (inner ℂ (hH.eigenvectorBasis i)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) H (hH.eigenvectorBasis i))).re = hH.eigenvalues i := by
  have he := hermitian_eigenbasis_energy H hH (hH.eigenvectorBasis.repr (hH.eigenvectorBasis i))
  simpa [OrthonormalBasis.repr_self, apply_ite] using! he

lemma matrix_rayleigh_convex_combination {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) ((a : ℂ) • H+(b : ℂ) • K) v)).re =
      a*(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re+
      b*(inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) K v)).re := by
  rw [map_add, map_smul, map_smul]
  change (inner ℂ v ((a : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)+
    (b : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) K v))).re = _
  rw [inner_add_right, inner_smul_right, inner_smul_right, Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Convexity of the trace spectral function follows from scalar Jensen,
without any differentiability or distinct-eigenvalue assumption. -/
lemma hermitian_spectral_sum_convex {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hM : ((a : ℂ) • H+(b : ℂ) • K).IsHermitian)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    (∑ i, f (hM.eigenvalues i)) ≤
      a*(∑ i, f (hH.eigenvalues i))+b*(∑ i, f (hK.eigenvalues i)) := by
  let e := hM.eigenvectorBasis
  have hpoint (i : Fin n) : f (hM.eigenvalues i) ≤
      a*f ((inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) H (e i))).re)+
      b*f ((inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) K (e i))).re) := by
    rw [← hermitian_eigenvector_energy _ hM i, matrix_rayleigh_convex_combination]
    exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hh
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hermitian_basis_jensen H hH f hf e) ha)
    (mul_le_mul_of_nonneg_left (hermitian_basis_jensen K hK f hf e) hb))

#print axioms hermitian_eigenvector_energy
#print axioms matrix_rayleigh_convex_combination
#print axioms hermitian_spectral_sum_convex
end SpectralRadiusUpperTail
