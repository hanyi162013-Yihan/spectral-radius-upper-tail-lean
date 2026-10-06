import SpectralRadiusUpperTail.IidSignedPairValue
import SpectralRadiusUpperTail.SignedMultiplicityCount

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
  [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma iidProperDoubleWord_expectation_one (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hp : (∫ z : 𝕂, z^2 ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (e : τ → σ) (s : τ → Bool)
    (hd : ∀ i, entryMultiplicity e i = 0 ∨ entryMultiplicity e i = 2)
    (hn : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) ≠ 0) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 1 := by
  apply iidSignedWord_pair_expectation_one μ hv e s
  intro i
  have hsum := signedMultiplicity_add e s i
  rcases hd i with hi | hi
  · left
    constructor <;> omega
  · right
    exact iidSignedWord_pair_balanced μ hp e s i (hsum.trans hi) hn

lemma iidRealDoubleWord_expectation_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hv : (∫ z : ℝ, ‖z‖^2 ∂μ) = 1) (e : τ → σ) (s : τ → Bool)
    (hd : ∀ i, entryMultiplicity e i = 0 ∨ entryMultiplicity e i = 2) :
    (∫ x : σ → ℝ, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) = 1 := by
  rw [iidSignedWord_expectation]
  apply Finset.prod_eq_one
  intro i _
  simp only [star_trivial, ← pow_add, signedMultiplicity_add]
  rcases hd i with hi | hi
  · simp [hi]
  · simpa only [hi, Real.norm_eq_abs, sq_abs] using hv

#print axioms iidProperDoubleWord_expectation_one
#print axioms iidRealDoubleWord_expectation_one
end SpectralRadiusUpperTail
