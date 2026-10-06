import SpectralRadiusUpperTail.GaussianSequentialL2
import SpectralRadiusUpperTail.KernelCenteringL2
import SpectralRadiusUpperTail.GaussianKernelTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

theorem gaussianSequentialIncrement_memLp_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    MemLp (gaussianSequentialIncrement μ v a N t n) 2
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
    gaussianSequentialRowLaw_probability μ v a ha N t n
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  rw [gaussianSequentialIncrement_eq_kernelCentered μ hX hm v a ha N t n hn]
  exact kernelCentered_memLp_two _ _ _
    (((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).stronglyMeasurable)
    (gaussianSequentialJoint_difference_memLp_two μ hX v a ha N t n hn)

/-- The actual discarded error is square integrable before conditional
expectation is used; no integrability of the desired matrix error is assumed. -/
theorem gaussianSequentialTruncationError_square_integrable
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun z => ‖gaussianSequentialIncrement μ v a N t n z-
      gaussianTruncatedSequentialIncrement μ v a N t n R z‖^2)
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
    gaussianSequentialRowLaw_probability μ v a ha N t n
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  have hb := gaussianTruncatedSequentialIncrement_basics μ hX v a ha N t n R hR
  have ht : MemLp (gaussianTruncatedSequentialIncrement μ v a N t n R) 2
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) :=
    MemLp.of_bound hb.1.aestronglyMeasurable (2*R) (Filter.Eventually.of_forall hb.2.2.2)
  have he := (gaussianSequentialIncrement_memLp_two μ hX hm v a ha N t n hn).sub ht
  exact (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he

#print axioms gaussianSequentialIncrement_memLp_two
#print axioms gaussianSequentialTruncationError_square_integrable
end SpectralRadiusUpperTail
