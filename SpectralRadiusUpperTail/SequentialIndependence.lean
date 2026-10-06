import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Independence.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

/-- If the second marginal of every conditional pair law is fixed, its
joint law with the entire preceding history is exactly the product law. -/
theorem compProd_comparator_joint (P : Measure Θ) [SFinite P]
    (κ : Kernel Θ (α × α)) [IsSFiniteKernel κ] (μ : Measure α) [SFinite μ]
    (hκ : ∀ s, (κ s).map Prod.snd = μ) :
    (P ⊗ₘ κ).map (fun z : Θ × (α × α) => (z.1,z.2.2)) = P.prod μ := by
  have hT : Measurable (fun z : Θ × (α × α) => (z.1,z.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  ext A hA
  rw [Measure.map_apply hT hA, Measure.compProd_apply (hT hA), Measure.prod_apply hA]
  apply lintegral_congr
  intro s
  have hs : MeasurableSet (Prod.mk s ⁻¹' A) := measurable_prodMk_left hA
  have h := congrArg (fun ν : Measure α => ν (Prod.mk s ⁻¹' A)) (hκ s)
  rw [Measure.map_apply measurable_snd hs] at h
  exact h

theorem compProd_comparator_independent (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ (α × α)) [IsMarkovKernel κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (hκ : ∀ s, (κ s).map Prod.snd = μ) :
    IndepFun (fun z : Θ × (α × α) => z.1) (fun z => z.2.2) (P ⊗ₘ κ) := by
  have hT : Measurable (fun z : Θ × (α × α) => (z.1,z.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hjoint := compProd_comparator_joint P κ μ hκ
  have hfirst := congrArg (fun ν : Measure (Θ × α) => ν.map Prod.fst) hjoint
  have hsecond := congrArg (fun ν : Measure (Θ × α) => ν.map Prod.snd) hjoint
  rw [Measure.map_map measurable_fst hT, Measure.map_fst_prod, measure_univ,
    one_smul] at hfirst
  rw [Measure.map_map measurable_snd hT, Measure.map_snd_prod, measure_univ,
    one_smul] at hsecond
  simp only [Function.comp_def] at hfirst hsecond
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    (measurable_snd.comp measurable_snd).aemeasurable).mpr
  simp only [Function.comp_def]
  rw [hfirst, hsecond]
  exact hjoint

#print axioms compProd_comparator_joint
#print axioms compProd_comparator_independent
end SpectralRadiusUpperTail
