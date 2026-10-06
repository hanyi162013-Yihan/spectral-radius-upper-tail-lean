import SpectralRadiusUpperTail.ComplexResidualSphereWitness
import SpectralRadiusUpperTail.SpectralUnitEigenvector

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma complex_eigenvalue_sphere_witness (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (x : Fin n → Fin n → ℂ) (ζ z : ℂ) (hζ : ζ ∈ spectrum ℂ (normalizedArray x))
    (δ : ℝ) (hδ : ‖ζ-z‖ ≤ δ) :
    ENNReal.ofReal (Real.exp (-(n : ℝ)*δ^2/u-(n : ℝ))*u^n/
      ‖(spectralResidualGram x z+((2*u : ℝ) : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).det‖) ≤ fullSpectralSphereWeight n u z x := by
  obtain ⟨v, hv, he⟩ := matrix_exists_unit_eigenvector (normalizedArray x) ζ hζ
  apply complex_residual_sphere_witness n hn u hu x z v hv (δ^2)
  rw [matrix_eigenvector_residual (normalizedArray x) ζ z v hv he]
  exact pow_le_pow_left₀ (norm_nonneg _) hδ 2

#print axioms complex_eigenvalue_sphere_witness
end SpectralRadiusUpperTail
