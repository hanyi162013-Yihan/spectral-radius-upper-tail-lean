import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

@[instance_reducible]
def historySigma : MeasurableSpace (Θ × α) :=
  MeasurableSpace.comap (Prod.fst : Θ × α → Θ) inferInstance

lemma historySigma_le : historySigma (Θ := Θ) (α := α) ≤
    (inferInstance : MeasurableSpace (Θ × α)) :=
  measurable_fst.comap_le

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Zero kernel means give an actual zero conditional expectation with
respect to the complete history sigma algebra. Integrability is explicit. -/
theorem condExp_history_eq_zero (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ))
    (hzero : ∀ᵐ s ∂P, (∫ x, f (s,x) ∂κ s) = 0) :
    (P ⊗ₘ κ)[f | historySigma] =ᵐ[P ⊗ₘ κ] 0 := by
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq historySigma_le hf ?_ ?_ ?_
  · intro A _ _
    exact integrableOn_zero
  · intro A hA _
    rcases (MeasurableSpace.measurableSet_comap.mp hA) with ⟨B,hB,rfl⟩
    simp only [Pi.zero_apply, integral_zero]
    rw [← Set.prod_univ]
    rw [Measure.setIntegral_compProd hB MeasurableSet.univ hf.integrableOn]
    simp only [Measure.restrict_univ]
    rw [integral_congr_ae (ae_restrict_of_ae hzero)]
    simp
  · exact aestronglyMeasurable_const

#print axioms condExp_history_eq_zero
end SpectralRadiusUpperTail
