import SpectralRadiusUpperTail.FutureWeight
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

lemma soft_exponential_integrable (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ) (hq : Measurable q) (hqn : ∀ x, 0 ≤ q x)
    (a : ℝ) (ha : 0 < a) : Integrable (fun x => Real.exp (-q x/a)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((Real.measurable_exp.comp (hq.neg.div_const a)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖Real.exp (-q x/a)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hqn x)) ha.le)

/-- Jensen gives a positive quantitative lower bound for a soft normalizer. -/
theorem soft_normalizer_jensen (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ) (hq : Measurable q) (hqi : Integrable q μ) (hqn : ∀ x, 0 ≤ q x)
    (a : ℝ) (ha : 0 < a) :
    Real.exp (-(∫ x, q x ∂μ)/a) ≤ ∫ x, Real.exp (-q x/a) ∂μ := by
  have h := convexOn_exp.map_integral_le (μ := μ) Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hqi.neg.div_const a) (soft_exponential_integrable μ q hq hqn a ha)
  simpa only [Pi.neg_apply, integral_div, integral_neg] using h

theorem soft_normalizer_lower (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ) (hq : Measurable q) (hqi : Integrable q μ) (hqn : ∀ x, 0 ≤ q x)
    (a M : ℝ) (ha : 0 < a) (hM : (∫ x, q x ∂μ) ≤ M) :
    Real.exp (-M/a) ≤ ∫ x, Real.exp (-q x/a) ∂μ :=
  (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hM) ha.le)).trans
    (soft_normalizer_jensen μ q hq hqi hqn a ha)

/-- The normalized likelihood is bounded uniformly using only a mean-energy bound. -/
theorem soft_normalized_likelihood_le (μ : Measure α) [IsProbabilityMeasure μ]
    (q : α → ℝ) (hq : Measurable q) (hqi : Integrable q μ) (hqn : ∀ x, 0 ≤ q x)
    (a M : ℝ) (ha : 0 < a) (hM : (∫ x, q x ∂μ) ≤ M) (x : α) :
    Real.exp (-q x/a) / (∫ y, Real.exp (-q y/a) ∂μ) ≤ Real.exp (M/a) := by
  have hlow := soft_normalizer_lower μ q hq hqi hqn a M ha hM
  have hZ := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hx : Real.exp (-q x/a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hqn x)) ha.le)
  calc
    _ ≤ 1 / Real.exp (-M/a) := div_le_div₀ (by positivity) hx (Real.exp_pos _) hlow
    _ = Real.exp (M/a) := by rw [neg_div, Real.exp_neg]; simp

#print axioms soft_normalizer_jensen
#print axioms soft_normalized_likelihood_le
end SpectralRadiusUpperTail
