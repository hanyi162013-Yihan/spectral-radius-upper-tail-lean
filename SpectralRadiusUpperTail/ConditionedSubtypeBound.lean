import SpectralRadiusUpperTail.ConditionedSubtypeMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma conditionedSubtypeMeasure_lintegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (S : Set E) (hS : MeasurableSet S)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : S, f x ∂conditionedSubtypeMeasure μ S) =
      (μ S)⁻¹ * ∫⁻ x in S, f x ∂μ := by
  rw [← lintegral_map hf measurable_subtype_coe,conditionedSubtypeMeasure_map μ S hS]
  simp only [ProbabilityTheory.cond,lintegral_smul_measure,smul_eq_mul]

lemma conditionedSubtypeMeasure_lintegral_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (S : Set E) (hS : MeasurableSet S)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : S, f x ∂conditionedSubtypeMeasure μ S) ≤
      (μ S)⁻¹ * ∫⁻ x, f x ∂μ := by
  rw [conditionedSubtypeMeasure_lintegral μ S hS f hf]
  exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

#print axioms conditionedSubtypeMeasure_lintegral
#print axioms conditionedSubtypeMeasure_lintegral_le
end SpectralRadiusUpperTail
