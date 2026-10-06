import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Measurability and exact averaging of a section probability under a
product probability law. This is the probabilistic fiber identity used in
the Talagrand induction. -/
theorem talagrand_fiber_mass_measurable_and_mean
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (α × β)) (hS : MeasurableSet S) :
    Measurable (fun x => ν.real (Prod.mk x ⁻¹' S)) ∧
    (∀ x, 0 ≤ ν.real (Prod.mk x ⁻¹' S) ∧
      ν.real (Prod.mk x ⁻¹' S) ≤ 1) ∧
    (∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ) = (μ.prod ν).real S := by
  have hm : Measurable (fun x => ν (Prod.mk x ⁻¹' S)) :=
    measurable_measure_prodMk_left hS
  have hrange : ∀ x, 0 ≤ ν.real (Prod.mk x ⁻¹' S) ∧
      ν.real (Prod.mk x ⁻¹' S) ≤ 1 := by
    intro x
    constructor
    · exact measureReal_nonneg
    · calc
        ν.real (Prod.mk x ⁻¹' S) ≤ ν.real Set.univ :=
          measureReal_mono (Set.subset_univ _)
        _ = 1 := by simp
  refine ⟨by simpa only [measureReal_def] using hm.ennreal_toReal,
    hrange, ?_⟩
  have hfinite : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) < ∞ :=
    Filter.Eventually.of_forall (fun x => lt_of_le_of_lt
      (measure_mono (Set.subset_univ _)) (by simp))
  calc
    (∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ) =
        (∫⁻ x, ν (Prod.mk x ⁻¹' S) ∂μ).toReal := by
          simpa only [measureReal_def] using
            (integral_toReal hm.aemeasurable hfinite)
    _ = (μ.prod ν).real S := by rw [measureReal_def, Measure.prod_apply hS]

#print axioms talagrand_fiber_mass_measurable_and_mean
end SpectralRadiusUpperTail
