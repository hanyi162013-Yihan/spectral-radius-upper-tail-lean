import SpectralRadiusUpperTail.GramDefectPatternBound
import SpectralRadiusUpperTail.ExtremalGramPatternCount

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

noncomputable abbrev ClosedDefectPattern (μ : Measure 𝕂) (s : Fin (2*r) → Bool) (g : ℕ) : Type := by
  classical
  exact {R : Setoid (Fin (2*r+1)) // orientedPatternMoment μ s R ≠ 0 ∧
    R.r (Fin.last (2*r)) 0 ∧ r+1-Nat.card (Quotient R) = g}

lemma closedDefectPattern_count_le_nonzero (μ : Measure 𝕂) (s : Fin (2*r) → Bool) (g : ℕ) :
    Nat.card (ClosedDefectPattern μ s g) ≤ Nat.card (NonzeroDefectPattern μ s g) := by
  classical
  let f : ClosedDefectPattern μ s g → NonzeroDefectPattern μ s g :=
    fun R => ⟨R.val,R.property.1,R.property.2.2⟩
  apply Nat.card_le_card_of_injective f
  intro R S h
  apply Subtype.ext
  exact congrArg (fun T => T.val) h

lemma closedDefectPattern_zero_count_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (s : Fin (2*r) → Bool) :
    Nat.card (ClosedDefectPattern μ s 0) ≤ Nat.card (ExtremalClosedPattern μ s) := by
  classical
  have hcard (R : ClosedDefectPattern μ s 0) : Nat.card (Quotient R.val) = r+1 := by
    have hle := orientedPatternMoment_nonzero_vertices μ hm s R.val R.property.1
    have hz := R.property.2.2
    simp only [Nat.card_eq_fintype_card] at hz ⊢
    omega
  let f : ClosedDefectPattern μ s 0 → ExtremalClosedPattern μ s :=
    fun R => ⟨R.val,R.property.1,hcard R,R.property.2.1⟩
  apply Nat.card_le_card_of_injective f
  intro R S h
  apply Subtype.ext
  exact congrArg (fun T => T.val) h

lemma closedGramDefectPattern_count_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (m q : ℕ) (hq : 1 ≤ q) (g : ℕ) (hg : g ≤ q*m) :
    Nat.card (ClosedDefectPattern μ (gramTreeSign m q) g) ≤
      (m+1)^(2*q) * (gramDefectCountBase m q)^g := by
  by_cases hg0 : g = 0
  · subst g
    simpa only [pow_zero,mul_one] using
      (closedDefectPattern_zero_count_le μ hm (gramTreeSign m q)).trans
        (extremalGramPattern_count_le μ hm m q)
  · exact (closedDefectPattern_count_le_nonzero μ (gramTreeSign m q) g).trans
      (gram_nonzeroDefectPattern_count_le_polynomial μ hm hq g (by omega) (by omega))

#print axioms ClosedDefectPattern
#print axioms closedDefectPattern_count_le_nonzero
#print axioms closedDefectPattern_zero_count_le
#print axioms closedGramDefectPattern_count_le
end SpectralRadiusUpperTail
