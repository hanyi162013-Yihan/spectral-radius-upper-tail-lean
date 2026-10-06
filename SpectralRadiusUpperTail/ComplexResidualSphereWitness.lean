import SpectralRadiusUpperTail.ComplexSphereWitness
import SpectralRadiusUpperTail.SphereResidualWeight

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma complex_residual_sphere_witness (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (x : Fin n → Fin n → ℂ) (z : ℂ) (v : EuclideanSpace ℂ (Fin n))
    (hv : ‖v‖ = 1) (d : ℝ)
    (hd : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x-z • 1) v‖^2 ≤ d) :
    ENNReal.ofReal (Real.exp (-(n : ℝ)*d/u-(n : ℝ))*u^n/
      ‖(spectralResidualGram x z+((2*u : ℝ) : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).det‖) ≤ fullSpectralSphereWeight n u z x := by
  rw [fullSphereWeight_eq_quadratic n hn u hu]
  apply complex_sphere_witness n hn u hu _ (spectralResidualGram_posSemidef x z) v hv d
  have he := matrix_gram_energy (normalizedArray x-z • (1 : Matrix (Fin n) (Fin n) ℂ)) v
  convert! he.le.trans hd using 1

#print axioms complex_residual_sphere_witness
end SpectralRadiusUpperTail
