import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma integral_closedBall_nat_tendsto (μ : Measure E) (f : E → ℝ) (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ x in closedBall (0 : E) (k : ℝ), f x ∂μ)
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hh := tendsto_setIntegral_of_monotone
    (fun k : ℕ => measurableSet_closedBall (x := (0 : E)) (ε := (k : ℝ)))
    (show Monotone (fun k : ℕ => closedBall (0 : E) (k : ℝ)) from
      fun i j hij => closedBall_subset_closedBall (by exact_mod_cast hij))
    (show IntegrableOn f (⋃ k : ℕ, closedBall (0 : E) (k : ℝ)) μ by
      simpa only [iUnion_closedBall_nat,integrableOn_univ] using hf)
  simpa only [iUnion_closedBall_nat,Measure.restrict_univ] using hh

lemma closedBall_probability_tendsto_one (μ : Measure E) [IsProbabilityMeasure μ] :
    Tendsto (fun k : ℕ => μ.real (closedBall (0 : E) (k : ℝ))) atTop (𝓝 1) := by
  simpa using integral_closedBall_nat_tendsto μ (fun _ => (1 : ℝ)) (integrable_const 1)

lemma conditional_integral_eq_div (μ : Measure E) (S : Set E) (f : E → ℝ) :
    (∫ x, f x ∂μ[|S]) = (∫ x in S, f x ∂μ)/μ.real S := by
  simp only [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,
    div_eq_mul_inv,Measure.real,mul_comm]

lemma conditional_closedBall_integral_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → ℝ) (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ x, f x ∂μ[|closedBall (0 : E) (k : ℝ)])
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  simp_rw [conditional_integral_eq_div]
  simpa only [div_one,Pi.div_def] using
    (integral_closedBall_nat_tendsto μ f hf).div (closedBall_probability_tendsto_one μ) (by norm_num)

lemma truncation_log_cost_tendsto_zero (μ : Measure E) [IsProbabilityMeasure μ] :
    Tendsto (fun k : ℕ => -Real.log (μ.real (closedBall (0 : E) (k : ℝ)))) atTop (𝓝 0) := by
  have hh := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (closedBall_probability_tendsto_one μ)
  simpa only [Real.log_one,neg_zero,Function.comp_def] using hh.neg

#print axioms integral_closedBall_nat_tendsto
#print axioms closedBall_probability_tendsto_one
#print axioms conditional_integral_eq_div
#print axioms conditional_closedBall_integral_tendsto
#print axioms truncation_log_cost_tendsto_zero
end SpectralRadiusUpperTail
