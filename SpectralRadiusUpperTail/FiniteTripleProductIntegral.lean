import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Regroup independent triples into three independent arrays. -/
theorem finite_triple_product_lintegral {ι : Type*} [Fintype ι]
    (μ ν κ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (κ i)]
    (F : (ι → ℝ × (ℝ × ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂Measure.pi (fun i => (μ i).prod ((ν i).prod (κ i)))) =
      ∫⁻ x, ∫⁻ u, ∫⁻ g, F (fun i => (x i,u i,g i))
        ∂Measure.pi κ ∂Measure.pi ν ∂Measure.pi μ := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℝ × ℝ) ι
  have hE := measurePreserving_arrowProdEquivProdArrow ℝ (ℝ × ℝ) ι μ (fun i => (ν i).prod (κ i))
  rw [MeasurePreserving.lintegral_map_equiv F E.symm hE.symm]
  change (∫⁻ z : (ι → ℝ) × (ι → ℝ × ℝ), F (fun i => (z.1 i,z.2 i))
    ∂(Measure.pi μ).prod (Measure.pi (fun i => (ν i).prod (κ i))))=_
  have hm : Measurable (fun z : (ι → ℝ) × (ι → ℝ × ℝ) => F (fun i => (z.1 i,z.2 i))) := by
    apply hF.comp
    fun_prop
  rw [lintegral_prod (fun z : (ι → ℝ) × (ι → ℝ × ℝ) => F (fun i => (z.1 i,z.2 i))) hm.aemeasurable]
  apply lintegral_congr
  intro x
  let E' := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι
  have hE' := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι ν κ
  rw [MeasurePreserving.lintegral_map_equiv (fun v : ι → ℝ × ℝ => F (fun i => (x i,v i))) E'.symm hE'.symm]
  change (∫⁻ z : (ι → ℝ) × (ι → ℝ), F (fun i => (x i,z.1 i,z.2 i))
    ∂(Measure.pi ν).prod (Measure.pi κ))=_
  apply lintegral_prod
  apply Measurable.aemeasurable
  apply hF.comp
  fun_prop

#print axioms finite_triple_product_lintegral
end SpectralRadiusUpperTail
