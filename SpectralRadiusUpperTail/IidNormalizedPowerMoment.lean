import SpectralRadiusUpperTail.NormalizedPowerBilinear

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

lemma normalizedPowerBilinear_sq_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (p q : Fin n → 𝕂) (k : ℕ) :
    Integrable (fun y => ‖normalizedPowerBilinear p q k y‖^2)
      (Measure.pi (fun _ : Fin n × Fin n => μ)) := by
  simp_rw [normalizedPowerBilinear_norm_sq]
  exact (norm_sq_integrable_of_mul_star
    (iidPowerBilinear_mul_star_integrable μ c hc hexp p q k)).const_mul _

/-- The actual normalized iid matrix power has a dimension-uniform O(1/n)
second moment for every pair of deterministic unit-energy vectors. -/
lemma normalizedPowerBilinear_secondMoment_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1) :
    (∫ y, ‖normalizedPowerBilinear p q k y‖^2
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)) ≤ pairedMomentConstant μ k/(n : ℝ) := by
  simp_rw [normalizedPowerBilinear_norm_sq]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (iidPowerBilinear_secondMoment_le μ c hc hexp hm hk hn p q hp hq)
    (show 0 ≤ (1/(n : ℝ))^k by positivity)
  exact h.trans_eq (inverse_power_cancellation hn hk _)

#print axioms normalizedPowerBilinear_sq_integrable
#print axioms normalizedPowerBilinear_secondMoment_le
end SpectralRadiusUpperTail
