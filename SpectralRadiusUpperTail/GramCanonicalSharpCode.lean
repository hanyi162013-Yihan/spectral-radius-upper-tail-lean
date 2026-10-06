import SpectralRadiusUpperTail.DefectSharpCode
import SpectralRadiusUpperTail.SharpDefectCodeCount
import SpectralRadiusUpperTail.GramIndexedMatchingCount
import SpectralRadiusUpperTail.CanonicalDefectCode

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {m q : ℕ}

def gramDefectMatchingCost (m q g : ℕ) := (m+1)^(2*q) * (2*(q*m)+1)^(8*g)

lemma gramPattern_exists_sharp_code (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hq : 1 ≤ q)
    (R : Setoid (Fin (2*(q*m)+1))) [DecidableRel R.r]
    (hn : orientedPatternMoment μ (gramTreeSign m q) R ≠ 0) :
    ∃ C : SharpDefectCode (gramTreeSign m q) (q*m+1-Fintype.card (Quotient R))
      (gramDefectMatchingCost m q (q*m+1-Fintype.card (Quotient R))), C.2.val.decode = R := by
  have hsur : Function.Surjective (Quotient.mk R) := by
    intro x
    exact Quotient.inductionOn x (fun a => ⟨a,rfl⟩)
  obtain ⟨c⟩ := orientedWalk_defect_route_certificate μ hm (gramTreeSign m q) (Quotient.mk R) hsur hn
  obtain ⟨C,hdec⟩ := c.exists_sharp_arrangement_code _ (c.gram_indexedMatching_count_le hq)
  have hsize : 2*(2*(q*m)) = 4*(q*m) := by omega
  refine ⟨⟨⟨c.segments.length,by have h := c.segment_budget; omega⟩,
    ⟨C.val,C.property.1,?_,C.property.2.2⟩⟩,?_⟩
  · simpa only [hsize] using C.property.2.1
  · exact hdec.trans (by apply Setoid.ext; intro a b; exact Quotient.eq)

lemma gram_nonzeroDefectPattern_count_le_explicit (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hq : 1 ≤ q) (g : ℕ) :
    Nat.card (NonzeroDefectPattern μ (gramTreeSign m q) g) ≤
      gramDefectMatchingCost m q g * defectCodeCost (2*(q*m)) g := by
  classical
  have hex (R : NonzeroDefectPattern μ (gramTreeSign m q) g) :
      ∃ C : SharpDefectCode (gramTreeSign m q) g (gramDefectMatchingCost m q g), C.2.val.decode = R.val := by
    rcases R with ⟨R,hn,hg⟩
    have h := gramPattern_exists_sharp_code μ hm hq R hn
    have hc : q*m+1-Fintype.card (Quotient R) = g := by
      simpa only [Nat.card_eq_fintype_card] using hg
    rw [hc] at h
    exact h
  let encode : NonzeroDefectPattern μ (gramTreeSign m q) g →
      SharpDefectCode (gramTreeSign m q) g (gramDefectMatchingCost m q g) :=
    fun R => Classical.choose (hex R)
  have hinj : Function.Injective encode := by
    intro R S h
    apply Subtype.ext
    exact (Classical.choose_spec (hex R)).symm.trans
      ((congrArg (fun C : SharpDefectCode (gramTreeSign m q) g (gramDefectMatchingCost m q g) =>
        C.2.val.decode) h).trans (Classical.choose_spec (hex S)))
  exact (Nat.card_le_card_of_injective encode hinj).trans
    (sharpDefectCode_count_le (gramTreeSign m q) g (gramDefectMatchingCost m q g))

#print axioms gramDefectMatchingCost
#print axioms gramPattern_exists_sharp_code
#print axioms gram_nonzeroDefectPattern_count_le_explicit
end SpectralRadiusUpperTail
