import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def conditionedSubtypeMeasure {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (S : Set E) : Measure S :=
  (μ S)⁻¹ • μ.comap Subtype.val

lemma conditionedSubtypeMeasure_map {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (S : Set E) (hS : MeasurableSet S) :
    (conditionedSubtypeMeasure μ S).map Subtype.val = μ[|S] := by
  rw [conditionedSubtypeMeasure,Measure.map_smul]
  rw [(measurePreserving_subtype_coe (μa := μ) hS).map_eq]
  rfl

lemma conditionedSubtypeMeasure_probability {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (S : Set E)
    (hS : MeasurableSet S) (hm : μ S ≠ 0) :
    IsProbabilityMeasure (conditionedSubtypeMeasure μ S) := by
  have hi := cond_isProbabilityMeasure hm
  constructor
  have he := congrArg (fun ρ : Measure E => ρ Set.univ) (conditionedSubtypeMeasure_map μ S hS)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,Set.preimage_univ,
    measure_univ] using he

lemma conditionedSubtypeMeasure_integral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (S : Set E) (hS : MeasurableSet S)
    (f : E → ℝ) (hf : Measurable f) :
    (∫ x : S, f x ∂conditionedSubtypeMeasure μ S) =
      (∫ x in S, f x ∂μ)/μ.real S := by
  rw [← integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable,
    conditionedSubtypeMeasure_map μ S hS]
  simp only [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,
    div_eq_mul_inv,Measure.real,mul_comm]

#print axioms conditionedSubtypeMeasure
#print axioms conditionedSubtypeMeasure_map
#print axioms conditionedSubtypeMeasure_probability
#print axioms conditionedSubtypeMeasure_integral
end SpectralRadiusUpperTail
