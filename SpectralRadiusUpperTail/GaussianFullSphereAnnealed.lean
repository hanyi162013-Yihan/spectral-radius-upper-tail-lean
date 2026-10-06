import SpectralRadiusUpperTail.FullSphereAnnealedIdentity
import SpectralRadiusUpperTail.GaussianNormalizerProducts
import SpectralRadiusUpperTail.ComplexUpperRateAlgebra

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Metric WithLp
open scoped ENNReal BigOperators

lemma gaussian_spectral_row_product {n : ℕ} (a : ℝ) (ha : 0 < a) (z : ℂ)
    (v : Fin n → ℂ) (hv : ∑ i, ‖v i‖^2 = 1) :
    (∏ i : Fin n, gaussianFiniteNormalizer properComplexGaussian a v
      (spectralTiltTarget z (zeroExtendVector v) i)) =
        Real.exp ((n : ℝ)*complexAnnealedExponent a ‖z‖) := by
  have hh := complex_gaussian_normalizer_product_log a ha v hv
    (spectralTiltTarget z (zeroExtendVector v))
  have he := spectralTiltTarget_energy (n := n) z (zeroExtendVector v)
    (by simpa only [zeroExtendVector_fin] using hv)
  rw [he] at hh
  have hp := gaussianMatrixWeight_integral_pos properComplexGaussian a ha v
    (spectralTiltTarget z (zeroExtendVector v))
  rw [gaussianMatrixWeight_integral] at hp
  apply Real.log_injOn_pos hp (Real.exp_pos _)
  rw [Real.log_exp, hh]
  dsimp [complexAnnealedExponent]
  ring

lemma gaussian_fullSphere_annealed (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a) (z : ℂ) :
    (∫⁻ x : Fin n → Fin n → ℂ, fullSpectralSphereWeight n a z x
      ∂Measure.pi (fun _ => Measure.pi (fun _ => properComplexGaussian))) =
        ENNReal.ofReal (Real.exp ((n : ℝ)*complexAnnealedExponent a ‖z‖)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace ℂ (Fin n)))
  rw [fullSphere_annealed_identity properComplexGaussian n hn a ha z, haarDirectionLaw]
  rw [lintegral_map (by
    simp_rw [properComplexGaussian_finite_normalizer a ha]
    simp only [spectralTiltTarget, zeroExtendVector_fin]
    fun_prop) (by fun_prop)]
  have he (v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1) :
      (∏ i : Fin n, gaussianFiniteNormalizer properComplexGaussian a (ofLp v.val)
        (spectralTiltTarget z (zeroExtendVector (ofLp v.val)) i)) =
          Real.exp ((n : ℝ)*complexAnnealedExponent a ‖z‖) := by
    apply gaussian_spectral_row_product a ha z
    rw [← EuclideanSpace.norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
    norm_num
  simp_rw [he]
  simp

#print axioms gaussian_spectral_row_product
#print axioms gaussian_fullSphere_annealed
end SpectralRadiusUpperTail
