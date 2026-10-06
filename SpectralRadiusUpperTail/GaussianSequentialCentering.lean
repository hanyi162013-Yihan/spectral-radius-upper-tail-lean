import SpectralRadiusUpperTail.GaussianSequentialIntegrability
import SpectralRadiusUpperTail.CouplingFirstMoment
import SpectralRadiusUpperTail.KernelCentering

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianSequentialIncrement (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂)) : 𝕂 :=
  z.2.1-z.2.2-∫ y : 𝕂, y ∂gaussianEntryLaw μ a
    (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
    (t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n z.1))

lemma gaussianSequentialKernel_difference_mean (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂) :
    Integrable (fun p : 𝕂 × 𝕂 => p.1-p.2) (gaussianSequentialKernel μ v a N t n s) ∧
      (∫ p, p.1-p.2 ∂gaussianSequentialKernel μ v a N t n s) =
      ∫ y : 𝕂, y ∂gaussianEntryLaw μ a (fun i : Fin (N-(n+1)) => v i.val)
        (v (N-(n+1))) (t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)) := by
  have hh := gaussianSequentialKernel_marginals μ hX v a ha N t n hn s
  let q := t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)
  have hi := gaussianEntryLaw_id_integrable μ hX a ha
    (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1))) q
    (gaussianEntryNormalizer_pos_recursive μ hX v (N-(n+1)) a ha q)
  have hc := coupling_difference_firstMoment _ μ (gaussianSequentialKernel μ v a N t n s)
    hh.1 hh.2 hi (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa only [hm, sub_zero] using hc

lemma gaussianSequentialIncrement_eq_kernelCentered (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    gaussianSequentialIncrement μ v a N t n =
      kernelCentered (gaussianSequentialKernel μ v a N t n)
        (fun z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) => z.2.1-z.2.2) := by
  funext z
  unfold gaussianSequentialIncrement kernelCentered
  rw [(gaussianSequentialKernel_difference_mean μ hX hm v a ha N t n hn z.1).2]

/-- The actual increment, centered by the actual conditional source mean, is
integrable and has zero conditional expectation given the full paired history. -/
theorem gaussianSequentialIncrement_condExp_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    Integrable (gaussianSequentialIncrement μ v a N t n)
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) ∧
    ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)[gaussianSequentialIncrement μ v a N t n | historySigma] =ᵐ[
        (gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n] 0 := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
    gaussianSequentialRowLaw_probability μ v a ha N t n
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  have hi := gaussianSequentialJoint_difference_integrable μ
    (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) v a ha N t n hn
  rw [gaussianSequentialIncrement_eq_kernelCentered μ hX hm v a ha N t n hn]
  exact ⟨kernelCentered_integrable _ _ _ hi, kernelCentered_condExp_zero _ _ _ hi⟩

#print axioms gaussianSequentialKernel_difference_mean
#print axioms gaussianSequentialIncrement_condExp_zero
end SpectralRadiusUpperTail
