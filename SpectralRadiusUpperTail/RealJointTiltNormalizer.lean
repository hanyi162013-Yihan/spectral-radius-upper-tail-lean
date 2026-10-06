import SpectralRadiusUpperTail.FlatSpectralJointTilt
import SpectralRadiusUpperTail.RealAnnealedNormalizer
import SpectralRadiusUpperTail.LogIntegralUniformBound
import SpectralRadiusUpperTail.NormalizedLogLimit
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

lemma real_joint_spectralTilt_logNormalizer_error
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L)
    (ν : Measure (flatUnitDirections ℝ n L)) [IsProbabilityMeasure ν] (b : ℝ) :
    |Real.log (∫ p, flatSpectralJointWeight a b p
      ∂ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))-
      (n : ℝ)*(Real.log (Real.sqrt (a/(a+2)))-b^2/(a+2))| ≤
      (n : ℝ)*gaussianNormalizerLogErrorConstant μ standardNormal a (‖b‖*L)*(L/Real.sqrt (n : ℝ)) := by
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
    exact real_spectralTilt_logNormalizer_error μ hm hvar c hc hexp
      a ha n L hL v.val (v.property.2.1 hn) v.property.2.2 b

lemma real_joint_spectralTilt_logNormalizer_limit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (L : ℝ) (hL : 0 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) :
    Tendsto (fun n => Real.log (∫ p, flatSpectralJointWeight a b p
      ∂(ν n).prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))/(n : ℝ))
      atTop (𝓝 (Real.log (Real.sqrt (a/(a+2)))-b^2/(a+2))) := by
  let C := gaussianNormalizerLogErrorConstant μ standardNormal a (‖b‖*L)
  apply normalized_log_tendsto_of_error _ (fun n => C*(L/Real.sqrt (n : ℝ)))
  · have ht : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using ht.const_mul C
  · intro n hn
    have hh := real_joint_spectralTilt_logNormalizer_error μ hm hvar c hc hexp
      a ha n hn L hL (ν n) b
    simpa only [C,mul_assoc] using hh

#print axioms real_joint_spectralTilt_logNormalizer_error
#print axioms real_joint_spectralTilt_logNormalizer_limit
end SpectralRadiusUpperTail
