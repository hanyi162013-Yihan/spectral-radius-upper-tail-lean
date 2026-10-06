import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma lowerFinset_eq_of_card_eq {α : Type*} [LinearOrder α] (s t : Finset α)
    (hs : IsLowerSet (s : Set α)) (ht : IsLowerSet (t : Set α))
    (hc : s.card = t.card) : s = t := by
  rcases hs.total ht with h | h
  · exact Finset.eq_of_subset_of_card_le h hc.ge
  · exact (Finset.eq_of_subset_of_card_le h hc.le).symm

/-- An initial segment of Fin m is encoded by its cardinality in Fin (m+1). -/
def initialSegmentCode {m : ℕ}
    (s : {s : Finset (Fin m) // IsLowerSet (s : Set (Fin m))}) : Fin (m+1) :=
  ⟨s.val.card, by have h := Finset.card_le_univ s.val; simpa using Nat.lt_succ_of_le h⟩

lemma initialSegmentCode_injective (m : ℕ) : Function.Injective (@initialSegmentCode m) := by
  intro s t h
  apply Subtype.ext
  apply lowerFinset_eq_of_card_eq s.val t.val s.property t.property
  exact congrArg Fin.val h

lemma initialSegment_count_le (m : ℕ) :
    Nat.card {s : Finset (Fin m) // IsLowerSet (s : Set (Fin m))} ≤ m+1 := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_injective (@initialSegmentCode m) (initialSegmentCode_injective m)

#print axioms lowerFinset_eq_of_card_eq
#print axioms initialSegmentCode
#print axioms initialSegmentCode_injective
#print axioms initialSegment_count_le
end SpectralRadiusUpperTail
