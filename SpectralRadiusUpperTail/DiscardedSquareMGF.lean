import SpectralRadiusUpperTail.TruncatedEntryLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

noncomputable def discardedSquare (R : ℝ) (x : E) : ℝ :=
  if R < ‖x‖ then ‖x‖^2 else 0

lemma discardedSquare_measurable (R : ℝ) : Measurable (discardedSquare (E := E) R) := by
  unfold discardedSquare
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    (measurable_norm.pow_const 2) measurable_const

lemma discardedSquare_bounds (R : ℝ) (x : E) :
    0 ≤ discardedSquare R x ∧ discardedSquare R x ≤ ‖x‖^2 := by
  by_cases h : R < ‖x‖ <;> simp [discardedSquare,h,sq_nonneg]

lemma discardedSquare_exp_integrable (μ : Measure E) (c R : ℝ) (hc : 0 ≤ c)
    (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    Integrable (fun x => Real.exp (c*discardedSquare R x)) μ := by
  apply hi.mono' (((discardedSquare_measurable R).const_mul c).exp.aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (discardedSquare_bounds R x).2 hc)

lemma discardedSquare_mgf_identity (μ : Measure E) [IsProbabilityMeasure μ]
    (c R : ℝ) (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    (∫ x, Real.exp (c*discardedSquare R x) ∂μ) =
      (∫ x, Real.exp (c*‖x‖^2) ∂μ)-
        ∫ x in closedBall 0 R, (Real.exp (c*‖x‖^2)-1) ∂μ := by
  have hf : Integrable (fun x : E => Real.exp (c*‖x‖^2)-1) μ := hi.sub (integrable_const (1 : ℝ))
  have hfi : Integrable ((closedBall (0 : E) R).indicator (fun x => Real.exp (c*‖x‖^2)-1)) μ :=
    hf.indicator measurableSet_closedBall
  have he (x : E) : Real.exp (c*discardedSquare R x) = Real.exp (c*‖x‖^2)-
      (closedBall (0 : E) R).indicator (fun x => Real.exp (c*‖x‖^2)-1) x := by
    by_cases hx : ‖x‖ ≤ R
    · simp [discardedSquare,not_lt.mpr hx,mem_closedBall,dist_zero_right,hx]
    · simp [discardedSquare,lt_of_not_ge hx,mem_closedBall,dist_zero_right,hx]
  simp_rw [he]
  rw [integral_sub hi hfi,integral_indicator measurableSet_closedBall]

lemma discardedSquare_mgf_tendsto_one (μ : Measure E) [IsProbabilityMeasure μ]
    (c : ℝ) (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    Tendsto (fun k : ℕ => ∫ x, Real.exp (c*discardedSquare (k : ℝ) x) ∂μ) atTop (𝓝 1) := by
  simp_rw [discardedSquare_mgf_identity μ c _ hi]
  have ht : Tendsto (fun _ : ℕ => ∫ x, Real.exp (c*‖x‖^2) ∂μ) atTop
      (𝓝 (∫ x, Real.exp (c*‖x‖^2) ∂μ)) := tendsto_const_nhds
  have hh := ht.sub (integral_closedBall_nat_tendsto μ
    (fun x : E => Real.exp (c*‖x‖^2)-1) (hi.sub (integrable_const 1)))
  simpa only [integral_sub hi (integrable_const (1 : ℝ)),integral_const,probReal_univ,
    smul_eq_mul,one_mul,sub_sub_cancel] using hh

lemma discardedSquare_log_mgf_tendsto_zero (μ : Measure E) [IsProbabilityMeasure μ]
    (c : ℝ) (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    Tendsto (fun k : ℕ => Real.log (∫ x, Real.exp (c*discardedSquare (k : ℝ) x) ∂μ))
      atTop (𝓝 0) := by
  simpa only [Real.log_one,Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      (discardedSquare_mgf_tendsto_one μ c hi)

#print axioms discardedSquare
#print axioms discardedSquare_measurable
#print axioms discardedSquare_bounds
#print axioms discardedSquare_exp_integrable
#print axioms discardedSquare_mgf_identity
#print axioms discardedSquare_mgf_tendsto_one
#print axioms discardedSquare_log_mgf_tendsto_zero
end SpectralRadiusUpperTail
