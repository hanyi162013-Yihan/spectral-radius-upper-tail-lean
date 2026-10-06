import SpectralRadiusUpperTail.GaussianTransitionDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Positivity of the actual finite normalizer for arbitrary coefficients. -/
lemma gaussianFiniteNormalizer_pos_future (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (s : 𝕂) :
    0 < gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s := by
  apply ENNReal.ofReal_pos.mp
  rw [← gaussianFutureWeight_eq_ofReal_finiteNormalizer μ v N a ha s]
  exact futureWeight_pos μ _ _ (fun _ => by fun_prop)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a) N s

/-- Normalizing the relative future likelihood cancels its base normalizer
pointwise and yields the exact entry density. -/
lemma gaussianEntryDensity_eq_futureRatio (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (N : ℕ)
    (a : ℝ) (ha : 0 < a) (s x : 𝕂) :
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N
    let g := fun x => (W (s-v N*x)).toReal/(W s).toReal
    ENNReal.ofReal (gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) (s-v N*x) /
      gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) (v N) s) =
        ENNReal.ofReal (g x/(∫ y, g y ∂μ)) := by
  dsimp only
  simp_rw [gaussianFutureWeight_eq_finiteNormalizer μ v N a ha]
  have hA := gaussianFiniteNormalizer_pos_future μ v N a ha s
  have hB := gaussianEntryNormalizer_pos_recursive μ hX v N a ha s
  rw [integral_div]
  congr 1
  change _ = (_/gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s)/
    (gaussianEntryNormalizer μ a (fun i : Fin N => v i.val) (v N) s/
      gaussianFiniteNormalizer μ a (fun i : Fin N => v i.val) s)
  field_simp

/-- Exact identity with the fixed likelihood coupling used by the quantitative
variance and exponential-tail estimates. -/
theorem gaussianSequentialKernel_eq_futureCoupling (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (N n : ℕ) (hn : n < N)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (s : Fin n → 𝕂 × 𝕂) :
    let q := t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)
    let W := futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) (N-(n+1))
    let g := fun x => (W (q-v (N-(n+1))*x)).toReal/(W q).toReal
    gaussianSequentialKernel μ v a N t n s =
      densityCoupling μ (fun x => ENNReal.ofReal (g x/(∫ y, g y ∂μ))) := by
  rw [gaussianSequentialKernel_eq_entryCoupling μ hX v N n hn a ha t s]
  congr 1
  funext x
  exact gaussianEntryDensity_eq_futureRatio μ hX v (N-(n+1)) a ha _ x

#print axioms gaussianSequentialKernel_eq_futureCoupling
end SpectralRadiusUpperTail
