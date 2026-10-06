import SpectralRadiusUpperTail.BoundedMedianRange
import Mathlib.Probability.CDF

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma real_probability_median_exists (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ m : ℝ, IsProbabilityMedian μ id m := by
  let S := {x : ℝ | 1/2 ≤ cdf μ x}
  obtain ⟨a, ha⟩ := ((tendsto_order.mp (tendsto_cdf_atBot μ)).2 (1/2) (by norm_num)).exists
  obtain ⟨b, hb⟩ := ((tendsto_order.mp (tendsto_cdf_atTop μ)).1 (1/2) (by norm_num)).exists
  have hSne : S.Nonempty := ⟨b, hb.le⟩
  have hSbb : BddBelow S := by
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hn
    have hxa := (monotone_cdf μ) (le_of_not_ge hn)
    change 1/2 ≤ cdf μ x at hx
    linarith
  let m := sInf S
  have hleft : ∀ x : ℝ, x < m → cdf μ x < 1/2 := by
    intro x hx
    by_contra hn
    have hh : m ≤ x := csInf_le hSbb (le_of_not_gt hn)
    linarith
  have hright : ∀ x : ℝ, m < x → 1/2 ≤ cdf μ x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hSne hx
    exact hy.trans ((monotone_cdf μ) hyx.le)
  have hmCDF : 1/2 ≤ cdf μ m := by
    rw [← (cdf μ).iInf_Ioi_eq m]
    exact le_ciInf (fun x => hright x x.property)
  have hmLeft : Function.leftLim (cdf μ) m ≤ 1/2 := by
    rw [(monotone_cdf μ).leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨cdf μ (m-1), m-1, by simp, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact (hleft x hx).le
  refine ⟨m, ?_, ?_⟩
  · simpa only [cdf_eq_real, id_eq, Set.mem_Iic] using! hmCDF
  · have hμ : μ (Ici m) = ENNReal.ofReal (1-Function.leftLim (cdf μ) m) := by
      conv_lhs => rw [← measure_cdf μ]
      exact (cdf μ).measure_Ici (tendsto_cdf_atTop μ) m
    change 1/2 ≤ (μ (Ici m)).toReal
    rw [hμ, ENNReal.toReal_ofReal (by linarith)]
    linarith

lemma probability_median_exists {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, IsProbabilityMedian μ f m := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  obtain ⟨m, hl, hu⟩ := real_probability_median_exists (μ.map f)
  refine ⟨m, ?_, ?_⟩
  · change (1/2 : ℝ) ≤ ((μ.map f) (Iic m)).toReal at hl
    rw [Measure.map_apply hf measurableSet_Iic] at hl
    exact hl
  · change (1/2 : ℝ) ≤ ((μ.map f) (Ici m)).toReal at hu
    rw [Measure.map_apply hf measurableSet_Ici] at hu
    exact hu

#print axioms real_probability_median_exists
#print axioms probability_median_exists
end SpectralRadiusUpperTail
