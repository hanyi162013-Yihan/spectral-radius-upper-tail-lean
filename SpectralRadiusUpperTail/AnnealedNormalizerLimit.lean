import SpectralRadiusUpperTail.ComplexAnnealedNormalizer
import SpectralRadiusUpperTail.RealAnnealedNormalizer
import SpectralRadiusUpperTail.GaussianMatrixWeight
import SpectralRadiusUpperTail.NormalizedLogLimit
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

lemma complex_annealed_matrix_normalizer_limit (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (v : (n : ℕ) → Fin n → ℂ)
    (hunit : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1)
    (hflat : ∀ n i, ‖v n i‖ ≤ L/Real.sqrt (n : ℝ)) (b : ℂ) :
    Tendsto (fun n => Real.log
      (∫ x : Fin n → Fin n → ℂ,
        gaussianMatrixWeight a (v n) (spectralTiltTarget b (zeroExtendVector (v n))) x
        ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))/(n : ℝ))
      atTop (𝓝 (Real.log (a/(a+1))-‖b‖^2/(a+1))) := by
  let C := gaussianNormalizerLogErrorConstant μ properComplexGaussian a (‖b‖*L)
  apply normalized_log_tendsto_of_error _ (fun n => C*(L/Real.sqrt (n : ℝ)))
  · have ht : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using ht.const_mul C
  · intro n hn
    rw [gaussianMatrixWeight_integral]
    have hh := complex_spectralTilt_logNormalizer_error μ hm hvar hpseudo c hc hexp
      a ha n L hL (v n) (hunit n hn) (hflat n) b
    simpa only [C,mul_assoc] using hh

lemma real_annealed_matrix_normalizer_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (v : (n : ℕ) → Fin n → ℝ)
    (hunit : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1)
    (hflat : ∀ n i, ‖v n i‖ ≤ L/Real.sqrt (n : ℝ)) (b : ℝ) :
    Tendsto (fun n => Real.log
      (∫ x : Fin n → Fin n → ℝ,
        gaussianMatrixWeight a (v n) (spectralTiltTarget b (zeroExtendVector (v n))) x
        ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))/(n : ℝ))
      atTop (𝓝 (Real.log (Real.sqrt (a/(a+2)))-b^2/(a+2))) := by
  let C := gaussianNormalizerLogErrorConstant μ standardNormal a (‖b‖*L)
  apply normalized_log_tendsto_of_error _ (fun n => C*(L/Real.sqrt (n : ℝ)))
  · have ht : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using ht.const_mul C
  · intro n hn
    rw [gaussianMatrixWeight_integral]
    have hh := real_spectralTilt_logNormalizer_error μ hm hvar c hc hexp
      a ha n L hL (v n) (hunit n hn) (hflat n) b
    simpa only [C,mul_assoc] using hh

#print axioms complex_annealed_matrix_normalizer_limit
#print axioms real_annealed_matrix_normalizer_limit
end SpectralRadiusUpperTail
