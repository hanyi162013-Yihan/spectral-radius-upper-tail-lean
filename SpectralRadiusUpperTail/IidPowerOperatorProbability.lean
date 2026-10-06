import SpectralRadiusUpperTail.IidNormalizedGramMoment
import SpectralRadiusUpperTail.OperatorTraceMarkov

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma normalizedPower_operator_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m k n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (hr : gramDefectRatio μ c m (2^(k+1)) n ≤ 1/2) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | R ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) ((normalizedIidMatrix x)^m)‖} ≤
      2*(n : ℝ)*(((m+1 : ℝ)/R)^2)^(2^(k+1)) := by
  apply (operator_probability_le_dyadic_trace (Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun x => (normalizedIidMatrix x)^m) k
    (normalizedGramTraceMoment_integrable μ c hc hexp m _ n) R hR).trans
  have hq : 1 ≤ 2^(k+1) := by
    have hp : (0 : ℕ) < 2^(k+1) := pow_pos (by decide) _
    omega
  have hh := normalizedGramTraceMoment_le_two μ c hc hexp hm hv m (2^(k+1)) n
    hq hn hr
  apply (div_le_div_of_nonneg_right hh (pow_nonneg hR.le _)).trans_eq
  rw [← pow_mul,div_pow]
  ring

#print axioms normalizedPower_operator_probability_le
end SpectralRadiusUpperTail
