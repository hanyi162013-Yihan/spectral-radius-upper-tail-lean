import SpectralRadiusUpperTail.IidProperSignedPair

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ComplexConjugate
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma iidSignedWord_pair_balanced (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hp : (∫ z : 𝕂, z^2 ∂μ) = 0) (e : τ → σ) (s : τ → Bool) (i : σ)
    (hcount : entryMultiplicity (fun t => (e t,s t)) (i,false) +
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 2)
    (hn : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) ≠ 0) :
    entryMultiplicity (fun t => (e t,s t)) (i,false) = 1 ∧
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 1 := by
  have he : entryMultiplicity (fun t => (e t,s t)) (i,false) =
      entryMultiplicity (fun t => (e t,s t)) (i,true) := by
    by_contra hne
    exact hn (iidSignedWord_improper_pair_zero μ hp e s i hcount hne)
  omega

lemma mixed_unit_pair_integral (μ : Measure 𝕂)
    (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1) :
    (∫ z : 𝕂, z * star z ∂μ) = 1 := by
  change (∫ z : 𝕂, z * conj z ∂μ) = 1
  simp_rw [RCLike.mul_conj, ← RCLike.ofReal_pow]
  rw [integral_ofReal, hv, RCLike.ofReal_one]

/-- A signed pairing with one occurrence of each sign has expectation exactly one. -/
lemma iidSignedWord_pair_expectation_one (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1) (e : τ → σ) (s : τ → Bool)
    (hpair : ∀ i, (entryMultiplicity (fun t => (e t,s t)) (i,false) = 0 ∧
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 0) ∨
      (entryMultiplicity (fun t => (e t,s t)) (i,false) = 1 ∧
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 1)) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 1 := by
  rw [iidSignedWord_expectation]
  apply Finset.prod_eq_one
  intro i _
  rcases hpair i with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp [ha,hb]
  · simpa only [ha,hb,pow_one] using mixed_unit_pair_integral μ hv

#print axioms iidSignedWord_pair_balanced
#print axioms mixed_unit_pair_integral
#print axioms iidSignedWord_pair_expectation_one
end SpectralRadiusUpperTail
