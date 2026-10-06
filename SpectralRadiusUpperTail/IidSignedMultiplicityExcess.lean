import SpectralRadiusUpperTail.SignedMultiplicityCount
import SpectralRadiusUpperTail.MultiplicityExcess
import SpectralRadiusUpperTail.IidSignedWordCancellation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma iidSignedWord_no_singleton (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (e : τ → σ) (s : τ → Bool)
    (hn : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) ≠ 0) (i : σ) :
    entryMultiplicity e i ≠ 1 := by
  intro hi
  apply hn
  apply iidSignedWord_singleton_zero μ hm e s i
  rw [signedMultiplicity_add, hi]

lemma iidSignedWord_excess_split (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (e : τ → σ) (s : τ → Bool)
    (hn : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) ≠ 0) :
    Fintype.card τ = (∑ i, if 0 < entryMultiplicity e i then 2 else 0) +
      ∑ i, (entryMultiplicity e i-2) := by
  rw [← entryMultiplicity_sum e]
  exact multiplicity_total_split _ (iidSignedWord_no_singleton μ hm e s hn)

#print axioms iidSignedWord_no_singleton
#print axioms iidSignedWord_excess_split
end SpectralRadiusUpperTail
