import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma log_shift_sub_log_tendsto (M : ℝ) :
    Tendsto (fun B : ℝ => Real.log (B+M)-Real.log B) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun B : ℝ => M/B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (fun B : ℝ => B) atTop atTop)
  have hr : Tendsto (fun B : ℝ => 1+M/B) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hdiv
  have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  simp only [Real.log_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-M))] with B hB
  have hB0 : 0 < B := (le_max_left _ _).trans_lt hB
  have hBM : 0 < B+M := by have := (le_max_right 0 (-M)).trans_lt hB; linarith
  change Real.log (1+M/B) = Real.log (B+M)-Real.log B
  rw [← Real.log_div (ne_of_gt hBM) (ne_of_gt hB0)]
  congr 1
  field_simp

lemma exists_large_log_normalization (b M ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, max b (max 0 M) < B ∧
      |Real.log (B-M)-Real.log B| < ε ∧
      |Real.log (B+M)-Real.log B| < ε := by
  have hm := (Metric.tendsto_nhds.mp (log_shift_sub_log_tendsto (-M))) ε hε
  have hp := (Metric.tendsto_nhds.mp (log_shift_sub_log_tendsto M)) ε hε
  obtain ⟨B, hB, hl, hu⟩ := ((eventually_gt_atTop (max b (max 0 M))).and (hm.and hp)).exists
  refine ⟨B, hB, ?_, ?_⟩
  · simpa [Real.dist_eq, sub_eq_add_neg] using hl
  · simpa [Real.dist_eq] using hu

#print axioms log_shift_sub_log_tendsto
#print axioms exists_large_log_normalization
end SpectralRadiusUpperTail
