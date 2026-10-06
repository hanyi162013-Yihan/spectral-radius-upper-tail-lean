import SpectralRadiusUpperTail.HermitianSpectralConvexity
import SpectralRadiusUpperTail.OrthonormalFrobeniusEnergy

namespace SpectralRadiusUpperTail
open scoped BigOperators NNReal Matrix.Norms.Frobenius

lemma matrix_rayleigh_sub {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) (H-K) v)).re =
      (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re-
      (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) K v)).re := by
  rw [map_sub]
  simp [inner_sub_right]

lemma hermitian_spectral_sum_sub_le {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (C : ℝ≥0) (hLip : LipschitzWith C f) :
    (∑ i, f (hH.eigenvalues i))-(∑ i, f (hK.eigenvalues i)) ≤
      (C : ℝ)*Real.sqrt (n : ℝ)*‖H-K‖ := by
  let e := hH.eigenvectorBasis
  have hJ := hermitian_basis_jensen K hK f hf e
  have hpoint (i : Fin n) :
      f (hH.eigenvalues i)-f ((inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) K (e i))).re) ≤
        (C : ℝ)*|(inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) (H-K) (e i))).re| := by
    have hh := hLip.norm_sub_le (hH.eigenvalues i)
      ((inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) K (e i))).re)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hh
    have he : hH.eigenvalues i-
        (inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) K (e i))).re =
        (inner ℂ (e i) (Matrix.toEuclideanCLM (𝕜 := ℂ) (H-K) (e i))).re := by
      rw [matrix_rayleigh_sub, hermitian_eigenvector_energy]
    rw [he] at hh
    exact (le_abs_self _).trans hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hdiag := mul_le_mul_of_nonneg_left (orthonormalBasis_diagonal_abs_sum (H-K) e) C.coe_nonneg
  rw [← mul_assoc] at hdiag
  linarith

lemma hermitian_spectral_sum_lipschitz {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (C : ℝ≥0) (hLip : LipschitzWith C f) :
    |(∑ i, f (hH.eigenvalues i))-(∑ i, f (hK.eigenvalues i))| ≤
      (C : ℝ)*Real.sqrt (n : ℝ)*‖H-K‖ := by
  have h1 := hermitian_spectral_sum_sub_le H K hH hK f hf C hLip
  have h2 := hermitian_spectral_sum_sub_le K H hK hH f hf C hLip
  rw [norm_sub_rev] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

#print axioms matrix_rayleigh_sub
#print axioms hermitian_spectral_sum_sub_le
#print axioms hermitian_spectral_sum_lipschitz
end SpectralRadiusUpperTail
