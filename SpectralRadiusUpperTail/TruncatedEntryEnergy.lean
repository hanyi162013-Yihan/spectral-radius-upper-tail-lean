import SpectralRadiusUpperTail.TruncatedEntryLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma conditional_ball_energy_memLp (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ) (hK : 0 ≤ K) :
    MemLp (fun x : E => ‖x‖^2) 2 μ[|closedBall (0 : E) K] := by
  apply MemLp.of_bound (continuous_norm.pow 2).measurable.aestronglyMeasurable (K^2)
  filter_upwards [ae_cond_mem (μ := μ) (measurableSet_closedBall (x := (0 : E)) (ε := K))] with x hx
  have hb : ‖x‖ ≤ K := by simpa only [mem_closedBall,dist_zero_right] using hx
  change ‖(‖x‖^2 : ℝ)‖ ≤ K^2
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x‖)]
  exact (sq_le_sq₀ (norm_nonneg x) hK).mpr hb

lemma good_entry_truncations_eventually (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : E => ‖x‖^2) μ) (hvar : (∫ x : E, ‖x‖^2 ∂μ) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      μ (closedBall (0 : E) (k : ℝ)) ≠ 0 ∧
      (1/2 : ℝ) < ∫ x : E, ‖x‖^2 ∂μ[|closedBall (0 : E) (k : ℝ)] ∧
      -Real.log (μ.real (closedBall (0 : E) (k : ℝ))) < ε := by
  have he := conditional_closedBall_integral_tendsto μ (fun x : E => ‖x‖^2) hi
  rw [hvar] at he
  have hm := (tendsto_order.1 (closedBall_probability_tendsto_one μ)).1 (1/2) (by norm_num)
  have hv := (tendsto_order.1 he).1 (1/2) (by norm_num)
  have hc := (tendsto_order.1 (truncation_log_cost_tendsto_zero μ)).2 ε hε
  filter_upwards [hm,hv,hc] with k hkm hkv hkc
  refine ⟨?_,hkv,hkc⟩
  intro hz
  simp only [Measure.real,hz,ENNReal.toReal_zero] at hkm
  linarith

#print axioms conditional_ball_energy_memLp
#print axioms good_entry_truncations_eventually
end SpectralRadiusUpperTail
