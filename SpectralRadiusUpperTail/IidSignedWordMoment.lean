import SpectralRadiusUpperTail.IidWordMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

/-- Group a signed iid word by the underlying entry and conjugation sign. -/
lemma signedWord_eq_mixed [CommSemiring 𝕂] [StarRing 𝕂]
    (e : τ → σ) (s : τ → Bool) (x : σ → 𝕂) :
    (∏ t, if s t then star (x (e t)) else x (e t)) =
      ∏ i, (x i)^(entryMultiplicity (fun t => (e t,s t)) (i,false)) *
        (star (x i))^(entryMultiplicity (fun t => (e t,s t)) (i,true)) := by
  have h := entryWord_product_eq_powers (fun t => (e t,s t))
    (fun z : σ × Bool => if z.2 then star (x z.1) else x z.1)
  simpa only [Fintype.prod_prod_type, Fintype.prod_bool, Bool.false_eq_true,
    if_false, if_true, mul_comm] using h

lemma iidSignedWord_integrable [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (e : τ → σ) (s : τ → Bool) :
    Integrable (fun x : σ → 𝕂 => ∏ t, if s t then star (x (e t)) else x (e t))
      (Measure.pi (fun _ : σ => μ)) := by
  simp_rw [signedWord_eq_mixed]
  exact iidMixedProduct_integrable μ c hc hexp _ _

lemma iidSignedWord_expectation [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (e : τ → σ) (s : τ → Bool) :
    (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) =
      ∏ i, ∫ z : 𝕂, z^(entryMultiplicity (fun t => (e t,s t)) (i,false)) *
        (star z)^(entryMultiplicity (fun t => (e t,s t)) (i,true)) ∂μ := by
  simp_rw [signedWord_eq_mixed]
  exact iidMixedProduct_expectation μ _ _

#print axioms signedWord_eq_mixed
#print axioms iidSignedWord_integrable
#print axioms iidSignedWord_expectation
end SpectralRadiusUpperTail
