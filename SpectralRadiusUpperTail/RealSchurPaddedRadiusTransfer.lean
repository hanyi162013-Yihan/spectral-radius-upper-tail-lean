import SpectralRadiusUpperTail.RealSchurPaddedCharpoly
import SpectralRadiusUpperTail.ExteriorSpectralRadius

namespace SpectralRadiusUpperTail
open scoped ENNReal NNReal Matrix.Norms.Frobenius

lemma flattenSchurBlocks_eigenvalue_le_radius {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (z : ℂ)
    (hz : z ∈ spectrum ℂ ((flattenSchurBlocks A).map Complex.ofRealHom)) :
    ‖z‖ ≤ (spectralRadius ℂ
      ((flattenSchurBlocks A).map Complex.ofRealHom)).toReal := by
  let M := (flattenSchurBlocks A).map Complex.ofRealHom
  have hbound : spectralRadius ℂ M ≤
      ENNReal.ofReal (‖M‖*‖(1 : Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ)‖) := by
    apply iSup₂_le
    intro w hw
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (spectrum.norm_le_norm_mul_of_mem hw)
  have hfinite : spectralRadius ℂ M ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hh : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ M :=
    le_iSup_of_le z (le_iSup_of_le hz le_rfl)
  simpa only [M, ENNReal.coe_toReal, coe_nnnorm] using
    ENNReal.toReal_mono hfinite hh

/-- A uniform bound on the spectra of the diagonal blocks bounds the radius
of the entire flattened triangular matrix. -/
theorem flattenSchurBlocks_upper_radius_le {N : ℕ}
    (A : Matrix (Fin N) (Fin N) (Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ i j, j < i → A i j = 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hblock : ∀ i (z : ℂ),
      z ∈ spectrum ℂ ((A i i).map Complex.ofRealHom) → ‖z‖ ≤ ρ) :
    (spectralRadius ℂ ((flattenSchurBlocks A).map Complex.ofRealHom)).toReal ≤ ρ := by
  have hs : spectralRadius ℂ ((flattenSchurBlocks A).map Complex.ofRealHom) ≤
      ENNReal.ofReal ρ := by
    apply iSup₂_le
    intro z hz
    obtain ⟨i, hi⟩ := flattenSchurBlocks_upper_spectrum A hA z hz
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hblock i z hi)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
  simpa only [ENNReal.toReal_ofReal hρ] using ht

#print axioms flattenSchurBlocks_upper_radius_le
#print axioms flattenSchurBlocks_eigenvalue_le_radius
end SpectralRadiusUpperTail
