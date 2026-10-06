import SpectralRadiusUpperTail.KernelTruncationMoments
import SpectralRadiusUpperTail.GaussianSequentialLocalMoments
import SpectralRadiusUpperTail.GaussianIncrementContinuity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianTruncatedSequentialIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (R : ℝ) :
    (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) → 𝕂 :=
  kernelCentered (gaussianSequentialKernel μ v a N t n)
    (kernelTruncated (gaussianSequentialIncrement μ v a N t n) R)

/-- The actual kernel truncation is jointly measurable, globally bounded and
conditionally centered under the actual history/next-step joint law. -/
theorem gaussianTruncatedSequentialIncrement_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    Measurable (gaussianTruncatedSequentialIncrement μ v a N t n R) ∧
      Integrable (gaussianTruncatedSequentialIncrement μ v a N t n R)
        ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) ∧
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)[
        gaussianTruncatedSequentialIncrement μ v a N t n R | historySigma] =ᵐ[
        (gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n] 0 ∧
      ∀ z, ‖gaussianTruncatedSequentialIncrement μ v a N t n R z‖ ≤ 2*R := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
    gaussianSequentialRowLaw_probability μ v a ha N t n
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  exact kernelTruncated_centered _ _ _
    (gaussianSequentialIncrement_continuous μ hX v a ha N t n).measurable R hR

/-- Actual conditional variance and discarded-error bounds at a history
where the already-proved local moments are available. -/
theorem gaussianTruncatedSequentialIncrement_conditional_moments
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂)
    (c M R : ℝ) (hc : 0 < c) (hR : 0 ≤ R)
    (he : Integrable (fun p => Real.exp (c*‖gaussianSequentialIncrement μ v a N t n (s,p)‖^2))
      (gaussianSequentialKernel μ v a N t n s))
    (hb : (∫ p, Real.exp (c*‖gaussianSequentialIncrement μ v a N t n (s,p)‖^2)
      ∂gaussianSequentialKernel μ v a N t n s) ≤ M) :
    (∫ p, ‖gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
      ∂gaussianSequentialKernel μ v a N t n s) ≤
      ∫ p, ‖gaussianSequentialIncrement μ v a N t n (s,p)‖^2
        ∂gaussianSequentialKernel μ v a N t n s ∧
      (∫ p, ‖gaussianSequentialIncrement μ v a N t n (s,p)-
        gaussianTruncatedSequentialIncrement μ v a N t n R (s,p)‖^2
        ∂gaussianSequentialKernel μ v a N t n s) ≤ (2/c)*Real.exp (-(c/2)*R^2)*M := by
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  have hf := (gaussianSequentialIncrement_continuous μ hX v a ha N t n).measurable
  have hfm : Measurable (fun p => gaussianSequentialIncrement μ v a N t n (s,p)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  obtain ⟨h1,h2⟩ := squareExp_moments (gaussianSequentialKernel μ v a N t n s) _
    hfm.aestronglyMeasurable c hc he
  have hz := gaussianSequentialIncrement_kernel_mean_zero μ hX hm v a ha N t n hn s
  exact ⟨(kernelTruncated_conditional_moments _ _ hf s h1 h2 hz R hR).1,
    kernelTruncated_conditional_error _ _ hf s hz c M R hc hR he hb⟩

#print axioms gaussianTruncatedSequentialIncrement_basics
#print axioms gaussianTruncatedSequentialIncrement_conditional_moments
end SpectralRadiusUpperTail
