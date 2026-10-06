import SpectralRadiusUpperTail.FlatSpectralJointTilt
import SpectralRadiusUpperTail.ComplexAnnealedNormalizer
import SpectralRadiusUpperTail.LogIntegralUniformBound
import SpectralRadiusUpperTail.NormalizedLogLimit
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

lemma complex_joint_spectralTilt_logNormalizer_error
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L)
    (ν : Measure (flatUnitDirections ℂ n L)) [IsProbabilityMeasure ν] (b : ℂ) :
    |Real.log (∫ p, flatSpectralJointWeight a b p
      ∂ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))-
      (n : ℝ)*(Real.log (a/(a+1))-‖b‖^2/(a+1))| ≤
      (n : ℝ)*gaussianNormalizerLogErrorConstant μ properComplexGaussian a (‖b‖*L)*(L/Real.sqrt (n : ℝ)) := by
  have hi := flatSpectralJointWeight_integrable μ ν a ha b
  rw [integral_prod _ hi]
  apply log_integral_error_of_uniform_log_error ν _ hi.integral_prod_left
  · intro v
    dsimp only [flatSpectralJointWeight]
    exact gaussianMatrixWeight_integral_pos μ a ha v.val (spectralTiltTarget (n := n) b (zeroExtendVector v.val))
  · intro v
    change |Real.log (∫ x, gaussianMatrixWeight a v.val
      (spectralTiltTarget b (zeroExtendVector v.val)) x
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))-_| ≤ _
    rw [gaussianMatrixWeight_integral]
    exact complex_spectralTilt_logNormalizer_error μ hm hvar hpseudo c hc hexp
      a ha n L hL v.val (v.property.2.1 hn) v.property.2.2 b

lemma complex_joint_spectralTilt_logNormalizer_limit
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) :
    Tendsto (fun n => Real.log (∫ p, flatSpectralJointWeight a b p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))/(n : ℝ))
      atTop (𝓝 (Real.log (a/(a+1))-‖b‖^2/(a+1))) := by
  let C := gaussianNormalizerLogErrorConstant μ properComplexGaussian a (‖b‖*L)
  apply normalized_log_tendsto_of_error _ (fun n => C*(L/Real.sqrt (n : ℝ)))
  · have ht : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using ht.const_mul C
  · intro n hn
    have hh := complex_joint_spectralTilt_logNormalizer_error μ hm hvar hpseudo c hc hexp
      a ha n hn L hL (ν n) b
    simpa only [C,mul_assoc] using hh

#print axioms complex_joint_spectralTilt_logNormalizer_error
#print axioms complex_joint_spectralTilt_logNormalizer_limit
end SpectralRadiusUpperTail
