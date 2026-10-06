import SpectralRadiusUpperTail.IidNormalizedPowerMoment
import SpectralRadiusUpperTail.SecondMomentProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {k n : ℕ}

lemma normalizedPowerBilinear_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hk : 0 < k) (hn : 0 < n)
    (p q : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {y | ε ≤ ‖normalizedPowerBilinear p q k y‖} ≤
        (pairedMomentConstant μ k/(n : ℝ))/ε^2 := by
  have h := norm_probability_le_secondMoment _ (normalizedPowerBilinear p q k)
    (normalizedPowerBilinear_sq_integrable μ c hc hexp p q k) ε hε
  exact h.trans (div_le_div_of_nonneg_right
    (normalizedPowerBilinear_secondMoment_le μ c hc hexp hm hk hn p q hp hq) (sq_nonneg ε))

/-- Every fixed positive power of the actual normalized centered iid matrix
has vanishing deterministic bilinear coefficients in probability. -/
lemma normalizedPowerBilinear_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (k : ℕ) (hk : 0 < k)
    (p q : (n : ℕ) → Fin n → 𝕂)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {y | ε ≤ ‖normalizedPowerBilinear (p n) (q n) k y‖}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact normalizedPowerBilinear_probability_le μ c hc hexp hm hk hn
      (p n) (q n) (hp n) (hq n) ε hε
  · have h : Tendsto (fun n : ℕ => pairedMomentConstant μ k/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [zero_div] using h.div_const (ε^2)

#print axioms normalizedPowerBilinear_probability_le
#print axioms normalizedPowerBilinear_probability_tendsto
end SpectralRadiusUpperTail
