import SpectralRadiusUpperTail.KernelCentering
import SpectralRadiusUpperTail.ExponentialTruncation
import Mathlib.Probability.Kernel.MeasurableIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def kernelTruncated (f : Θ × α → E) (R : ℝ) : Θ × α → E :=
  {z | ‖f z‖ ≤ R}.indicator f

lemma kernelTruncated_measurable (f : Θ × α → E) (hf : Measurable f) (R : ℝ) :
    Measurable (kernelTruncated f R) :=
  hf.indicator (measurableSet_le hf.norm measurable_const)

lemma kernelTruncated_norm_le (f : Θ × α → E) (R : ℝ) (hR : 0 ≤ R) (z : Θ × α) :
    ‖kernelTruncated f R z‖ ≤ R := by
  by_cases hz : ‖f z‖ ≤ R
  · change ‖{z | ‖f z‖ ≤ R}.indicator f z‖ ≤ R
    rw [Set.indicator_of_mem (show z ∈ {z | ‖f z‖ ≤ R} from hz)]
    exact hz
  · change ‖{z | ‖f z‖ ≤ R}.indicator f z‖ ≤ R
    rw [Set.indicator_of_notMem (show z ∉ {z | ‖f z‖ ≤ R} from hz), norm_zero]
    exact hR

lemma kernelCentered_measurable (κ : Kernel Θ α) [IsSFiniteKernel κ]
    (f : Θ × α → E) (hf : Measurable f) : Measurable (kernelCentered κ f) := by
  have hmean : StronglyMeasurable (fun s => ∫ x, f (s,x) ∂κ s) :=
    hf.stronglyMeasurable.integral_kernel_prod_right'
  exact hf.sub (hmean.measurable.comp measurable_fst)

lemma kernelTruncated_joint_integrable (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E) (hf : Measurable f)
    (R : ℝ) (hR : 0 ≤ R) : Integrable (kernelTruncated f R) (P ⊗ₘ κ) :=
  (integrable_const R).mono' (kernelTruncated_measurable f hf R).aestronglyMeasurable
    (Filter.Eventually.of_forall (kernelTruncated_norm_le f R hR))

/-- Conditional recentering of the bounded actual truncation is measurable,
bounded by twice the cutoff, and has zero conditional expectation. -/
theorem kernelTruncated_centered (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E) (hf : Measurable f)
    (R : ℝ) (hR : 0 ≤ R) :
    Measurable (kernelCentered κ (kernelTruncated f R)) ∧
      Integrable (kernelCentered κ (kernelTruncated f R)) (P ⊗ₘ κ) ∧
      (P ⊗ₘ κ)[kernelCentered κ (kernelTruncated f R) | historySigma] =ᵐ[P ⊗ₘ κ] 0 ∧
      ∀ z, ‖kernelCentered κ (kernelTruncated f R) z‖ ≤ 2*R := by
  have hi := kernelTruncated_joint_integrable P κ f hf R hR
  refine ⟨kernelCentered_measurable κ _ (kernelTruncated_measurable f hf R),
    kernelCentered_integrable P κ _ hi, kernelCentered_condExp_zero P κ _ hi, ?_⟩
  intro z
  have hm : ‖∫ x, kernelTruncated f R (z.1,x) ∂κ z.1‖ ≤ R := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := κ z.1)
      (Filter.Eventually.of_forall (fun x => kernelTruncated_norm_le f R hR (z.1,x)))
  exact (norm_sub_le _ _).trans (by linarith [kernelTruncated_norm_le f R hR z])

#print axioms kernelTruncated_centered
end SpectralRadiusUpperTail
