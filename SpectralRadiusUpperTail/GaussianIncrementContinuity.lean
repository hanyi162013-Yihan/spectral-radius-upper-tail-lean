import SpectralRadiusUpperTail.GaussianSequentialCentering
import SpectralRadiusUpperTail.GaussianEntryContinuity

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Continuity of the actual sequential centered increment. The recursively
proved positive entry normalizer supplies the mean denominator at every target. -/
theorem gaussianSequentialIncrement_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) : Continuous (gaussianSequentialIncrement μ v a N t n) := by
  have hmean := gaussianEntryLaw_mean_continuous μ hX a ha
    (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
    (gaussianEntryNormalizer_pos_recursive μ hX v (N-(n+1)) a ha)
  have ht : Continuous (fun z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) =>
      t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n z.1)) := by
    unfold revealedSum coordinateVector
    fun_prop
  exact (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
    |>.sub (hmean.comp ht)

#print axioms gaussianSequentialIncrement_continuous
end SpectralRadiusUpperTail
