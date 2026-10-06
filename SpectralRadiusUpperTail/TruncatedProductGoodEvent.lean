import SpectralRadiusUpperTail.TruncatedEntryEnergy
import SpectralRadiusUpperTail.IidAverageLower
import SpectralRadiusUpperTail.PiConditionedLaw
import SpectralRadiusUpperTail.TiltGoodIntersection

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma truncated_product_good_event_half (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ) (hK : 0 ≤ K) (hmass : μ (closedBall (0 : E) K) ≠ 0)
    (hmean : (1/2 : ℝ) < ∫ x : E, ‖x‖^2 ∂μ[|closedBall (0 : E) K]) :
    ∀ᶠ n : ℕ in atTop,
      1/2 ≤ (Measure.pi (fun _ : Fin n => μ[|closedBall (0 : E) K])).real
        ((Set.univ.pi (fun _ : Fin n => closedBall (0 : E) K)) ∩
          {x | (n : ℝ)/4 < ∑ i : Fin n, ‖x i‖^2}) := by
  let S := closedBall (0 : E) K
  letI : IsProbabilityMeasure μ[|S] := cond_isProbabilityMeasure hmass
  have hA (n : ℕ) : MeasurableSet (Set.univ.pi (fun _ : Fin n => S)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hB (n : ℕ) : MeasurableSet {x : Fin n → E | (n : ℝ)/4 < ∑ i, ‖x i‖^2} := by
    apply measurableSet_lt measurable_const
    fun_prop
  apply probability_inter_eventually_half (fun n => Fin n → E)
    (fun n => Measure.pi (fun _ : Fin n => μ[|S]))
    (fun n => Set.univ.pi (fun _ : Fin n => S))
    (fun n => {x | (n : ℝ)/4 < ∑ i : Fin n, ‖x i‖^2}) hA hB
  · have hz (n : ℕ) : (Measure.pi (fun _ : Fin n => μ[|S])).real
        ((Set.univ.pi (fun _ : Fin n => S))ᶜ) = 0 := by
      rw [Measure.real,prob_compl_eq_one_sub (hA n),Measure.pi_pi]
      simp [S,cond_apply_self hmass (measure_ne_top μ S)]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have ht := iid_sum_lower_probability_tendsto μ[|S] (fun x : E => ‖x‖^2)
      (conditional_ball_energy_memLp μ K hK) (1/4) (by dsimp only [S]; linarith)
    simpa only [Set.compl_setOf,not_lt,div_eq_mul_inv,one_div,one_mul] using ht

lemma original_truncated_good_event_lower (μ : Measure E) [IsProbabilityMeasure μ]
    (K : ℝ) (hK : 0 ≤ K) (hmass : μ (closedBall (0 : E) K) ≠ 0)
    (hmean : (1/2 : ℝ) < ∫ x : E, ‖x‖^2 ∂μ[|closedBall (0 : E) K]) :
    ∀ᶠ n : ℕ in atTop,
      (μ.real (closedBall (0 : E) K))^n/2 ≤
        (Measure.pi (fun _ : Fin n => μ)).real
          ((Set.univ.pi (fun _ : Fin n => closedBall (0 : E) K)) ∩
            {x | (n : ℝ)/4 < ∑ i : Fin n, ‖x i‖^2}) := by
  have ht := truncated_product_good_event_half μ K hK hmass hmean
  filter_upwards [ht] with n hn
  let S := closedBall (0 : E) K
  let G : Set (Fin n → E) := (Set.univ.pi (fun _ : Fin n => S)) ∩
    {x | (n : ℝ)/4 < ∑ i : Fin n, ‖x i‖^2}
  have hG : MeasurableSet G := by
    apply (MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)).inter
    apply measurableSet_lt measurable_const
    fun_prop
  have he := pi_conditioned_event μ S measurableSet_closedBall n G hG
  rw [Set.inter_eq_left.mpr Set.inter_subset_left] at he
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow] at her
  have hpos : 0 < (μ.real S)^n :=
    pow_pos (ENNReal.toReal_pos hmass (measure_ne_top _ _)) n
  change 1/2 ≤ (Measure.pi (fun _ : Fin n => μ[|S])).real G at hn
  rw [show (Measure.pi (fun _ : Fin n => μ[|S])).real G =
      (Measure.pi (fun _ : Fin n => μ)).real G/(μ.real S)^n from her] at hn
  have hh := (le_div_iff₀ hpos).mp hn
  change (μ.real S)^n/2 ≤ (Measure.pi (fun _ : Fin n => μ)).real G
  linarith

#print axioms truncated_product_good_event_half
#print axioms original_truncated_good_event_lower
end SpectralRadiusUpperTail
