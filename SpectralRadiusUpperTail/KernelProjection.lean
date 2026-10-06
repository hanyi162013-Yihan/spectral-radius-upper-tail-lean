import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {Θ Λ α β : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
  [MeasurableSpace α] [MeasurableSpace β]

/-- A projection preserves the prescribed transition law when every projected
conditional kernel depends only on the projected history. -/
theorem compProd_projection (P : Measure Θ) [SFinite P]
    (κ : Kernel Θ α) [IsSFiniteKernel κ]
    (η : Kernel Λ β) [IsSFiniteKernel η]
    (f : Θ → Λ) (g : α → β) (hf : Measurable f) (hg : Measurable g)
    (hκ : ∀ s, (κ s).map g = η (f s)) :
    (P ⊗ₘ κ).map (Prod.map f g) = (P.map f) ⊗ₘ η := by
  ext A hA
  rw [Measure.map_apply (hf.prodMap hg) hA,
    Measure.compProd_apply ((hf.prodMap hg) hA), Measure.compProd_apply hA,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) hf]
  apply lintegral_congr
  intro s
  have h := congrArg (fun ν : Measure β => ν (Prod.mk (f s) ⁻¹' A)) (hκ s)
  rw [Measure.map_apply hg (measurable_prodMk_left hA)] at h
  exact h

#print axioms compProd_projection
end SpectralRadiusUpperTail
