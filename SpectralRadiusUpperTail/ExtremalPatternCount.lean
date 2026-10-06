import SpectralRadiusUpperTail.CanonicalMatchingInjective
import SpectralRadiusUpperTail.ExtremalSignedMatching
import SpectralRadiusUpperTail.GramSignMatchingCount

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

noncomputable abbrev ExtremalClosedPattern (μ : Measure 𝕂) (s : Fin (2*r) → Bool) : Type := by
  classical
  exact {R : Setoid (Fin (2*r+1)) // orientedPatternMoment μ s R ≠ 0 ∧
    Nat.card (Quotient R) = r+1 ∧ R.r (Fin.last (2*r)) 0}

lemma extremalPattern_has_matching (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) (R : ExtremalClosedPattern μ s) :
    ∃ f : SignedNoncrossingMatching s, ∀ i,
      orientedWalkEdge s (Quotient.mk R.val) (f.val.val i) =
        orientedWalkEdge s (Quotient.mk R.val) i := by
  classical
  apply orientedWalk_extremal_signed_matching μ hm s (Quotient.mk R.val) _ R.property.1
    (by simpa only [Nat.card_eq_fintype_card] using R.property.2.1)
    (Quotient.sound R.property.2.2)
  intro x
  exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)

noncomputable def extremalPatternMatching (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) (R : ExtremalClosedPattern μ s) :
    SignedNoncrossingMatching s := Classical.choose (extremalPattern_has_matching μ hm s R)

lemma extremalPatternMatching_injective (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) :
    Function.Injective (extremalPatternMatching μ hm s) := by
  classical
  intro R S he
  have hfR := Classical.choose_spec (extremalPattern_has_matching μ hm s R)
  have hfS := Classical.choose_spec (extremalPattern_has_matching μ hm s S)
  change ∀ i, orientedWalkEdge s (Quotient.mk R.val) ((extremalPatternMatching μ hm s R).val.val i) =
    orientedWalkEdge s (Quotient.mk R.val) i at hfR
  change ∀ i, orientedWalkEdge s (Quotient.mk S.val) ((extremalPatternMatching μ hm s S).val.val i) =
    orientedWalkEdge s (Quotient.mk S.val) i at hfS
  rw [he] at hfR
  apply Subtype.ext
  exact orientedPattern_eq_of_same_matching μ hm s R.val S.val R.property.1 S.property.1
    (by simpa only [Nat.card_eq_fintype_card] using R.property.2.1)
    (by simpa only [Nat.card_eq_fintype_card] using S.property.2.1)
    (extremalPatternMatching μ hm s S).val.val (extremalPatternMatching μ hm s S).val.property.2.1
    hfR hfS

lemma extremalPattern_count_le_matching (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) :
    Nat.card (ExtremalClosedPattern μ s) ≤ Nat.card (SignedNoncrossingMatching s) := by
  classical
  exact Nat.card_le_card_of_injective _ (extremalPatternMatching_injective μ hm s)

#print axioms ExtremalClosedPattern
#print axioms extremalPattern_has_matching
#print axioms extremalPatternMatching
#print axioms extremalPatternMatching_injective
#print axioms extremalPattern_count_le_matching
end SpectralRadiusUpperTail
