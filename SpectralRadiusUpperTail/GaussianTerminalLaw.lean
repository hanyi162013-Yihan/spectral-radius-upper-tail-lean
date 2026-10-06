import SpectralRadiusUpperTail.FinitePathStep
import SpectralRadiusUpperTail.GaussianSequentialCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma gaussianSequentialRowLaw_eq_finiteCoupledLaw (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) :
    gaussianSequentialRowLaw μ v a N t n =
      finiteCoupledLaw (gaussianSequentialKernel μ v a N t) n := rfl

/-- Each actual paired history is the corresponding suffix marginal of the
same terminal Gaussian-soft coupled row. -/
theorem gaussianSequentialRowLaw_suffix (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n ≤ N) :
    (gaussianSequentialRowLaw μ v a N t N).map (pathSuffix N n hn) =
      gaussianSequentialRowLaw μ v a N t n := by
  have (k : ℕ) : IsMarkovKernel (gaussianSequentialKernel μ v a N t k) :=
    gaussianSequentialKernel_markov μ v a ha N t k
  simp only [gaussianSequentialRowLaw_eq_finiteCoupledLaw]
  exact finiteCoupledLaw_suffix _ N n hn

/-- This terminal projection has the actual history/kernel joint law, so it
preserves the conditional structure used to center the next increment. -/
theorem gaussianSequentialRowLaw_step (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    (gaussianSequentialRowLaw μ v a N t N).map (pathStep N n hn) =
      (gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n := by
  have (k : ℕ) : IsMarkovKernel (gaussianSequentialKernel μ v a N t k) :=
    gaussianSequentialKernel_markov μ v a ha N t k
  simp only [gaussianSequentialRowLaw_eq_finiteCoupledLaw]
  exact finiteCoupledLaw_step _ N n hn

#print axioms gaussianSequentialRowLaw_step
end SpectralRadiusUpperTail
