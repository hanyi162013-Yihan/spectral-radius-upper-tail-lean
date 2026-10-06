import SpectralRadiusUpperTail.GaussianSequentialCoupling

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Pointwise density identity, stronger than equality of the source marginals. -/
lemma gaussianRevealedDensity_eq_entryDensity (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (N n : ℕ) (hn : n < N)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (s : Fin n → 𝕂) (x : 𝕂) :
    doobDensity N (revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t) n s x =
      ENNReal.ofReal (gaussianFiniteNormalizer μ a (fun i : Fin (N-(n+1)) => v i.val)
        (t-revealedSum (fun i x => v i*x) N n s-v (N-(n+1))*x) /
        gaussianEntryNormalizer μ a (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
          (t-revealedSum (fun i x => v i*x) N n s)) := by
  symm
  have hB := gaussianEntryNormalizer_pos_recursive μ hX v (N-(n+1)) a ha
    (t-revealedSum (fun i x => v i*x) N n s)
  rw [ENNReal.ofReal_div_of_pos hB,
    gaussianEntryNormalizer_ofReal_eq_future μ hX v (N-(n+1)) a ha,
    ← gaussianFutureWeight_eq_ofReal_finiteNormalizer μ v (N-(n+1)) a ha]
  have hindex : N-n = N-(n+1)+1 := by omega
  simp only [doobDensity, if_pos hn, revealedWeight]
  rw [revealedSum_cons _ N n hn, add_comm (v (N-(n+1))*x), sub_add_eq_sub_sub, hindex]

/-- The actual transition is the explicit density coupling of the actual
conditional entry density, not an arbitrary coupling with those marginals. -/
theorem gaussianSequentialKernel_eq_entryCoupling (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (N n : ℕ) (hn : n < N)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (s : Fin n → 𝕂 × 𝕂) :
    gaussianSequentialKernel μ v a N t n s =
      densityCoupling μ (fun x => ENNReal.ofReal
        (gaussianFiniteNormalizer μ a (fun i : Fin (N-(n+1)) => v i.val)
          (t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)-v (N-(n+1))*x) /
          gaussianEntryNormalizer μ a (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
            (t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)))) := by
  change densityCoupling μ _ = _
  congr 1
  funext x
  exact gaussianRevealedDensity_eq_entryDensity μ hX v N n hn a ha t _ x

#print axioms gaussianSequentialKernel_eq_entryCoupling
end SpectralRadiusUpperTail
