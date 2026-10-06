import SpectralRadiusUpperTail.GaussianEntryFutureBridge

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma gaussianFutureWeight_eq_ofReal_finiteNormalizer (μ : Measure 𝕂)
    [IsProbabilityMeasure μ] (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (s : 𝕂) :
    futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N s =
      ENNReal.ofReal (gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s) := by
  rw [gaussianFutureWeight_eq_convolution μ v N a ha,
    gaussianFiniteNormalizer_eq_convolution]
  rfl

/-- The entry normalizer is exactly the next recursive future weight, in the
same descending coordinate order as the sequential coupling. -/
lemma gaussianEntryNormalizer_ofReal_eq_future (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (s : 𝕂) :
    ENNReal.ofReal (gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) (v N) s) =
      futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) (N+1) s := by
  have hf := gaussianEntry_weight_measurable μ hX a ha (fun i : Fin N => v i.val) (v N) s
  have hb (x : 𝕂) : |gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) (s-v N*x)| ≤ 1 := by
    rw [abs_of_nonneg (gaussianFiniteNormalizer_bounds μ a ha _ _).1]
    exact (gaussianFiniteNormalizer_bounds μ a ha _ _).2
  have hi := (bounded_weight_projection_integrable μ hX _ hf hb (0 : 𝕂)).1
  rw [gaussianEntryNormalizer, ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => (gaussianFiniteNormalizer_bounds μ a ha _ _).1))]
  simp only [futureWeight]
  apply lintegral_congr
  intro x
  exact (gaussianFutureWeight_eq_ofReal_finiteNormalizer μ v N a ha _).symm

/-- Every transition denominator is positive for every history. -/
lemma gaussianEntryNormalizer_pos_recursive (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (s : 𝕂) :
    0 < gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) (v N) s := by
  apply ENNReal.ofReal_pos.mp
  rw [gaussianEntryNormalizer_ofReal_eq_future μ hX v N a ha]
  exact futureWeight_pos μ _ _ (fun _ => by fun_prop)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a) _ _

/-- The actual regression entry law is exactly the Doob transition used by
the existing two-marginal coupling. At step n, coordinate N-(n+1) is current. -/
theorem gaussianEntryLaw_eq_revealed_transition (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (v : ℕ → 𝕂) (N n : ℕ) (hn : n < N) (a : ℝ) (ha : 0 < a)
    (t : 𝕂) (s : Fin n → 𝕂) :
    gaussianEntryLaw μ a (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
        (t-revealedSum (fun i x => v i*x) N n s) =
      μ.withDensity (doobDensity N
        (revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t) n s) := by
  have hB := gaussianEntryNormalizer_pos_recursive μ hX v (N-(n+1)) a ha
    (t-revealedSum (fun i x => v i*x) N n s)
  unfold gaussianEntryLaw
  congr 1
  funext x
  rw [ENNReal.ofReal_div_of_pos hB,
    gaussianEntryNormalizer_ofReal_eq_future μ hX v (N-(n+1)) a ha,
    ← gaussianFutureWeight_eq_ofReal_finiteNormalizer μ v (N-(n+1)) a ha]
  have hm : N-n = N-(n+1)+1 := by omega
  simp only [doobDensity, if_pos hn, revealedWeight]
  rw [revealedSum_cons _ N n hn, add_comm (v (N-(n+1))*x), sub_add_eq_sub_sub, hm]

#print axioms gaussianEntryNormalizer_ofReal_eq_future
#print axioms gaussianEntryLaw_eq_revealed_transition
end SpectralRadiusUpperTail
