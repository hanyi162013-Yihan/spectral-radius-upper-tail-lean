import SpectralRadiusUpperTail.NormalizedMatrixTrace
import SpectralRadiusUpperTail.FiniteAverageSecondMoment
import SpectralRadiusUpperTail.IidCoefficientPower
import SpectralRadiusUpperTail.NormalizedPowerMeasurable

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma normalizedTrace_power_eq_average {n : ℕ} (k : ℕ) (x : Fin n × Fin n → 𝕂) :
    normalizedMatrixTrace ((normalizedIidMatrix x)^k) =
      (n : 𝕂)⁻¹ * ∑ i, normalizedPowerBilinear (Pi.single i 1) (Pi.single i 1) k x := by
  simp_rw [← matrixCoefficient_normalized_power, matrixCoefficient_coordinate]
  rfl

lemma measurable_normalizedTrace_power (n k : ℕ) :
    Measurable (fun x : Fin n × Fin n → 𝕂 => normalizedMatrixTrace ((normalizedIidMatrix x)^k)) := by
  simp_rw [normalizedTrace_power_eq_average]
  exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
    measurable_normalizedPowerBilinear (Pi.single i 1) (Pi.single i 1) k))

lemma iidTracePower_secondMoment (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    Integrable (fun x => ‖normalizedMatrixTrace ((normalizedIidMatrix x)^k)‖^2)
      (Measure.pi (fun _ : Fin n × Fin n => μ)) ∧
    (∫ x, ‖normalizedMatrixTrace ((normalizedIidMatrix x)^k)‖^2
      ∂Measure.pi (fun _ : Fin n × Fin n => μ)) ≤ pairedMomentConstant μ k/(n : ℝ) := by
  have hmeas := (measurable_normalizedTrace_power (𝕂 := 𝕂) n k).norm.pow_const 2
  simp_rw [normalizedTrace_power_eq_average] at hmeas ⊢
  exact integral_average_sq_le hn _ _
    (fun i => normalizedPowerBilinear_sq_integrable μ c hc hexp _ _ k)
    hmeas.aestronglyMeasurable _ (fun i =>
      normalizedPowerBilinear_secondMoment_le μ c hc hexp hm hk hn _ _
        (coordinateVector_energy i).le (coordinateVector_energy i).le)

lemma iidTracePower_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ε ≤ ‖normalizedMatrixTrace ((normalizedIidMatrix x)^k)‖}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hh := iidTracePower_secondMoment μ c hc hexp hm n k hn hk
    exact (norm_probability_le_secondMoment _ _ hh.1 ε hε).trans
      (div_le_div_of_nonneg_right hh.2 (sq_nonneg ε))
  · have h : Tendsto (fun n : ℕ => pairedMomentConstant μ k/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [zero_div] using h.div_const (ε^2)

#print axioms normalizedTrace_power_eq_average
#print axioms measurable_normalizedTrace_power
#print axioms iidTracePower_secondMoment
#print axioms iidTracePower_probability_tendsto
end SpectralRadiusUpperTail
