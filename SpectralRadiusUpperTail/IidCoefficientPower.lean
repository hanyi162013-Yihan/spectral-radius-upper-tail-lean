import SpectralRadiusUpperTail.MatrixCoefficient
import SpectralRadiusUpperTail.IidNormalizedGramMoment
import SpectralRadiusUpperTail.IidNormalizedPowerProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma matrixCoefficient_normalized_power {n : ℕ} (p q : Fin n → 𝕂) (k : ℕ)
    (x : Fin n × Fin n → 𝕂) :
    matrixCoefficient p q ((normalizedIidMatrix x)^k) = normalizedPowerBilinear p q k x := by
  rw [matrixCoefficient_eq_sum]
  rfl

lemma iidCoefficient_power_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (k : ℕ) (hk : 0 < k)
    (p q : (n : ℕ) → Fin n → 𝕂)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ε ≤ ‖matrixCoefficient (p n) (q n) ((normalizedIidMatrix x)^k)‖}) atTop (𝓝 0) := by
  simp_rw [matrixCoefficient_normalized_power]
  exact normalizedPowerBilinear_probability_tendsto μ c hc hexp hm k hk p q hp hq ε hε

#print axioms matrixCoefficient_normalized_power
#print axioms iidCoefficient_power_probability_tendsto
end SpectralRadiusUpperTail
