import SpectralRadiusUpperTail.GaussianLogProductComparison
import SpectralRadiusUpperTail.GaussianNormalizerProducts

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma complex_spectralTilt_logNormalizer_error (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (v : Fin n → ℂ) (hv : (∑ i, ‖v i‖^2) = 1)
    (hflat : ∀ i, ‖v i‖ ≤ L/Real.sqrt (n : ℝ)) (b : ℂ) :
    |Real.log (∏ i : Fin n, gaussianFiniteNormalizer μ a v (spectralTiltTarget b (zeroExtendVector v) i))-
      (n : ℝ)*(Real.log (a/(a+1))-‖b‖^2/(a+1))| ≤
        (n : ℝ)*gaussianNormalizerLogErrorConstant μ properComplexGaussian a (‖b‖*L)*
          (L/Real.sqrt (n : ℝ)) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ c hc hexp 2)
  let t : Fin n → ℂ := spectralTiltTarget b (zeroExtendVector v)
  have hflat' : ∀ i : Fin n, ‖zeroExtendVector v i.val‖ ≤ L/Real.sqrt (n : ℝ) := by
    simpa only [zeroExtendVector_fin] using hflat
  have hh := gaussianNormalizer_product_log_comparison_flat μ properComplexGaussian
    hX properComplexGaussian_memLp hm properComplexGaussian_mean hvar properComplexGaussian_energy
    (hpseudo.trans properComplexGaussian_pseudo.symm)
    (squareExp_norm_pow_integrable μ c hc hexp 3) properComplexGaussian_third_integrable
    a ha n v hv.le (L/Real.sqrt (n : ℝ)) (by positivity) hflat t (‖b‖*L)
    (fun i => spectralTiltTarget_bound b (zeroExtendVector v) L hflat' i)
  have henergy : (∑ i, ‖t i‖^2) = (n : ℝ)*‖b‖^2 :=
    spectralTiltTarget_energy b (zeroExtendVector v) (by simpa only [zeroExtendVector_fin] using hv)
  have he : Real.log (∏ i : Fin n, gaussianFiniteNormalizer properComplexGaussian a v (t i)) =
      (n : ℝ)*(Real.log (a/(a+1))-‖b‖^2/(a+1)) := by
    rw [complex_gaussian_normalizer_product_log a ha v hv t,henergy]
    ring
  rw [he] at hh
  exact hh

#print axioms complex_spectralTilt_logNormalizer_error
end SpectralRadiusUpperTail
