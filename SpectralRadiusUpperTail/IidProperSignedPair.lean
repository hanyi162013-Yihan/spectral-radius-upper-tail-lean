import SpectralRadiusUpperTail.IidSignedWordCancellation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ComplexConjugate
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma proper_mixed_pair_zero (μ : Measure 𝕂)
    (hp : (∫ z : 𝕂, z^2 ∂μ) = 0) (a b : ℕ)
    (hab : a+b=2) (hne : a ≠ b) :
    (∫ z : 𝕂, z^a * (star z)^b ∂μ) = 0 := by
  have hcases : (a=2 ∧ b=0) ∨ (a=0 ∧ b=2) := by omega
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simpa only [pow_zero, mul_one] using hp
  · simp only [pow_zero, one_mul]
    have h : (∫ z : 𝕂, conj (z^2) ∂μ) = 0 := by rw [integral_conj, hp, map_zero]
    simpa only [map_pow, starRingEnd_apply] using h

/-- Under properness, an entry appearing twice with the same sign contributes zero. -/
lemma iidSignedWord_improper_pair_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hp : (∫ z : 𝕂, z^2 ∂μ) = 0) (e : τ → σ) (s : τ → Bool) (i : σ)
    (hcount : entryMultiplicity (fun t => (e t,s t)) (i,false) +
      entryMultiplicity (fun t => (e t,s t)) (i,true) = 2)
    (hne : entryMultiplicity (fun t => (e t,s t)) (i,false) ≠
      entryMultiplicity (fun t => (e t,s t)) (i,true)) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 0 := by
  exact iidSignedWord_zero_factor μ e s i (proper_mixed_pair_zero μ hp _ _ hcount hne)

#print axioms proper_mixed_pair_zero
#print axioms iidSignedWord_improper_pair_zero
end SpectralRadiusUpperTail
