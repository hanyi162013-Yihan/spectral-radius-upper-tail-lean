import SpectralRadiusUpperTail.TruncatedEntryLimit
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma positive_energy_truncations_eventually (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : E => ‖x‖^2) μ)
    (hvar : (1/2 : ℝ) < ∫ x : E, ‖x‖^2 ∂μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      μ (closedBall (0 : E) (k : ℝ)) ≠ 0 ∧
      (1/2 : ℝ) < ∫ x : E, ‖x‖^2 ∂μ[|closedBall (0 : E) (k : ℝ)] ∧
      -Real.log (μ.real (closedBall (0 : E) (k : ℝ))) < ε := by
  have he := conditional_closedBall_integral_tendsto μ (fun x : E => ‖x‖^2) hi
  have hm := (tendsto_order.1 (closedBall_probability_tendsto_one μ)).1 (1/2) (by norm_num)
  have hv := (tendsto_order.1 he).1 (1/2) hvar
  have hc := (tendsto_order.1 (truncation_log_cost_tendsto_zero μ)).2 ε hε
  filter_upwards [hm,hv,hc] with k hkm hkv hkc
  refine ⟨?_,hkv,hkc⟩
  intro hz
  simp only [Measure.real,hz,ENNReal.toReal_zero] at hkm
  linarith

#print axioms positive_energy_truncations_eventually
end SpectralRadiusUpperTail
