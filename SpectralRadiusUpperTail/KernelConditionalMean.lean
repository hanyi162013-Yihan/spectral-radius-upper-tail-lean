import SpectralRadiusUpperTail.KernelCentering
import Mathlib.Probability.Kernel.MeasurableIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Conditional expectation under an actual history/kernel joint law is its
actual kernel integral, not merely zero for a centered special case. -/
theorem condExp_history_eq_kernelMean (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : StronglyMeasurable f) (hi : Integrable f (P ⊗ₘ κ)) :
    (P ⊗ₘ κ)[f | historySigma] =ᵐ[P ⊗ₘ κ]
      fun z => ∫ x, f (z.1,x) ∂κ z.1 := by
  let g := fun z : Θ × α => ∫ x, f (z.1,x) ∂κ z.1
  have hg : StronglyMeasurable[historySigma] g :=
    hf.integral_kernel_prod_right'.comp_measurable (comap_measurable Prod.fst)
  have hgi : Integrable g (P ⊗ₘ κ) := kernelMean_lift_integrable P κ f hi
  have hc := kernelCentered_condExp_zero P κ f hi
  have he : kernelCentered κ f = f-g := rfl
  rw [he] at hc
  have hs := condExp_sub hi hgi historySigma
  rw [condExp_of_stronglyMeasurable historySigma_le hg hgi] at hs
  filter_upwards [hs,hc] with z hz hc
  exact sub_eq_zero.mp (hz.symm.trans hc)

#print axioms condExp_history_eq_kernelMean
end SpectralRadiusUpperTail
