import SpectralRadiusUpperTail.IidSignedWordMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- A centered iid entry occurring just once annihilates a signed word. -/
lemma iidSignedWord_singleton_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (e : τ → σ) (s : τ → Bool) (i : σ)
    (hi : entryMultiplicity (fun t => (e t,s t)) (i,false) +
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 1) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 0 := by
  simp_rw [signedWord_eq_mixed]
  exact iidMixedProduct_singleton_zero μ hm _ _ i hi

/-- Vanishing of one scalar mixed moment annihilates the full actual word expectation. -/
lemma iidSignedWord_zero_factor (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (e : τ → σ) (s : τ → Bool) (i : σ)
    (hi : (∫ z : 𝕂, z^(entryMultiplicity (fun t => (e t,s t)) (i,false)) *
      (star z)^(entryMultiplicity (fun t => (e t,s t)) (i,true)) ∂μ) = 0) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 0 := by
  rw [iidSignedWord_expectation]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

#print axioms iidSignedWord_singleton_zero
#print axioms iidSignedWord_zero_factor
end SpectralRadiusUpperTail
