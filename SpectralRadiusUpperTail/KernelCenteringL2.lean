import SpectralRadiusUpperTail.KernelConditionalMean
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual kernel centering preserves L2: its mean is the proved conditional
expectation, to which the L2 contraction theorem applies. -/
theorem kernelCentered_memLp_two (P : Measure Θ) [IsProbabilityMeasure P]
    (κ : Kernel Θ α) [IsMarkovKernel κ] (f : Θ × α → E)
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 (P ⊗ₘ κ)) :
    MemLp (kernelCentered κ f) 2 (P ⊗ₘ κ) := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hce : MemLp ((P ⊗ₘ κ)[f | historySigma]) 2 (P ⊗ₘ κ) :=
    hf.condExp (by norm_num)
  have he := condExp_history_eq_kernelMean P κ f hfm hi
  exact hf.sub (hce.ae_eq he)

#print axioms kernelCentered_memLp_two
end SpectralRadiusUpperTail
