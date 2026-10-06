import SpectralRadiusUpperTail.IidPowerOperatorProbability
import SpectralRadiusUpperTail.GramDefectRatioLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The needed fixed-power upper input, derived from actual iid Gram moments. -/
lemma normalizedPower_operator_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m : ℕ) (R : ℝ) (hR : (m+1 : ℝ) < R) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | R ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) ((normalizedIidMatrix x)^m)‖})
      atTop (𝓝 0) := by
  have hR0 : 0 < R := lt_trans (by positivity) hR
  have ha0 : 0 ≤ (m+1 : ℝ)/R := div_nonneg (by positivity) hR0.le
  have ha1 : (m+1 : ℝ)/R < 1 := (div_lt_one hR0).mpr hR
  have hs : ((m+1 : ℝ)/R)^2 < 1 := pow_lt_one₀ ha0 ha1 (by decide)
  have ht := (dyadicMomentOrder_tail_tendsto 80 (by decide)
    (((m+1 : ℝ)/R)^2) (sq_nonneg _) hs).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _
    (show Tendsto (fun n : ℕ => 2*(n : ℝ)*(((m+1 : ℝ)/R)^2)^(dyadicMomentOrder 80 n))
      atTop (𝓝 0) by simpa only [mul_assoc] using ht)
  filter_upwards [gramDefectRatio_dyadic_eventually μ c hc m,
    eventually_ge_atTop (1 : ℕ)] with n hratio hn
  exact normalizedPower_operator_probability_le μ c hc hexp hm hv m
    (Nat.log 2 n / 80) n hn R hR0 hratio

#print axioms normalizedPower_operator_probability_tendsto
end SpectralRadiusUpperTail
