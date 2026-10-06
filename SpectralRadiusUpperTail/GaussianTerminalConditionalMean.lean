import SpectralRadiusUpperTail.KernelConditionalMean
import SpectralRadiusUpperTail.ConditionalValuePullback
import SpectralRadiusUpperTail.GaussianTerminalLaw
import SpectralRadiusUpperTail.FinitePathFiltration

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
variable {𝕂 E : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual terminal conditional expectation of any integrable step
function is the actual next-transition kernel integral at its terminal history. -/
theorem gaussianTerminal_condExp_step (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N)
    (f : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) → E) (hf : StronglyMeasurable f)
    (hi : Integrable f ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)) :
    (gaussianSequentialRowLaw μ v a N t N)[f ∘ pathStep N n hn | pathFiltration N n] =ᵐ[
      gaussianSequentialRowLaw μ v a N t N]
        fun x => ∫ p, f (pathSuffix N n hn.le x,p)
          ∂gaussianSequentialKernel μ v a N t n (pathSuffix N n hn.le x) := by
  have (k : ℕ) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t k) :=
    gaussianSequentialRowLaw_probability μ v a ha N t k
  have (k : ℕ) : IsMarkovKernel (gaussianSequentialKernel μ v a N t k) :=
    gaussianSequentialKernel_markov μ v a ha N t k
  let g := fun z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) =>
    ∫ p, f (z.1,p) ∂gaussianSequentialKernel μ v a N t n z.1
  have hg : StronglyMeasurable[historySigma] g :=
    hf.integral_kernel_prod_right'.comp_measurable (comap_measurable Prod.fst)
  have hh := condExp_pullback_eq (gaussianSequentialRowLaw μ v a N t N)
    ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)
    (pathStep N n hn) (pathStep_measurable N n hn)
    (gaussianSequentialRowLaw_step μ v a ha N t n hn) historySigma historySigma_le
    f g hi (kernelMean_lift_integrable _ _ f hi) hg
    (condExp_history_eq_kernelMean _ _ f hf hi)
  rw [pathStep_historySigma] at hh
  exact hh

#print axioms gaussianTerminal_condExp_step
end SpectralRadiusUpperTail
