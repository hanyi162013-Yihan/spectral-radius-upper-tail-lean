import SpectralRadiusUpperTail.ConditionalMean

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma kernelMean_integrable (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ)) :
    Integrable (fun s => ∫ x, f (s,x) ∂κ s) P := by
  have h : Integrable f ((Kernel.const Unit P ⊗ₖ Kernel.prodMkLeft Unit κ) ()) := hf
  simpa only [Kernel.prodMkLeft_apply, Kernel.const_apply] using h.integral_compProd

lemma kernelMean_lift_integrable (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ)) :
    Integrable (fun z : Θ × α => ∫ x, f (z.1,x) ∂κ z.1) (P ⊗ₘ κ) := by
  have hfst : MeasurePreserving (Prod.fst : Θ × α → Θ) (P ⊗ₘ κ) P :=
    ⟨measurable_fst, Measure.fst_compProd P κ⟩
  simpa only [Function.comp_def] using
    hfst.integrable_comp_of_integrable (kernelMean_integrable P κ f hf)

noncomputable def kernelCentered (κ : Kernel Θ α) (f : Θ × α → E) (z : Θ × α) : E :=
  f z - ∫ x, f (z.1,x) ∂κ z.1

lemma kernelCentered_integrable (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ)) :
    Integrable (kernelCentered κ f) (P ⊗ₘ κ) :=
  hf.sub (kernelMean_lift_integrable P κ f hf)

lemma kernelCentered_mean_zero (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ)) :
    ∀ᵐ s ∂P, (∫ x, kernelCentered κ f (s,x) ∂κ s) = 0 := by
  have h := ((Measure.integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1
  filter_upwards [h] with s hs
  simp only [kernelCentered]
  rw [integral_sub hs (integrable_const _)]
  simp

/-- Centering each transition by its actual kernel mean creates a zero
conditional expectation relative to the entire preceding history. -/
theorem kernelCentered_condExp_zero (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hf : Integrable f (P ⊗ₘ κ)) :
    (P ⊗ₘ κ)[kernelCentered κ f | historySigma] =ᵐ[P ⊗ₘ κ] 0 :=
  condExp_history_eq_zero P κ _ (kernelCentered_integrable P κ f hf)
    (kernelCentered_mean_zero P κ f hf)

#print axioms kernelCentered_condExp_zero
end SpectralRadiusUpperTail
