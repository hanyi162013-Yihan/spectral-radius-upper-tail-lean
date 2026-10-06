import SpectralRadiusUpperTail.MarkedChunkCode
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace SpectralRadiusUpperTail
variable {A : Type*} [Fintype A]

/-- Nonempty ordered chunks of total length n are encoded by n symbols,
each carrying one boundary bit. Empty outer lists are included when n=0. -/
lemma nonemptyChunk_count_le (n : ℕ) :
    Nat.card {C : List (List A) // (∀ l ∈ C, l ≠ []) ∧ C.flatten.length = n} ≤
      (2*Fintype.card A)^n := by
  classical
  let P := {C : List (List A) // (∀ l ∈ C, l ≠ []) ∧ C.flatten.length = n}
  let encode : P → (Fin n → A × Bool) := fun p i =>
    (markChunkEnds p.val).get ⟨i.val,by rw [markChunkEnds_length,p.property.2]; exact i.isLt⟩
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply Subtype.ext
    apply markChunkEnds_injective p.property.1 q.property.1
    apply List.ext_getElem
    · rw [markChunkEnds_length,markChunkEnds_length,p.property.2,q.property.2]
    · intro i hi hj
      have hi' : i < n := by simpa only [markChunkEnds_length,p.property.2] using hi
      exact congrFun hpq ⟨i,hi'⟩
  have h := Nat.card_le_card_of_injective encode hinj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    mul_comm] using h

/-- Segment numbering, whole-segment reversal bits and tour boundaries have
at most (4S)^S possibilities when S segments are used once in total. -/
lemma rearrangementShape_count_le (S : ℕ) :
    Nat.card {C : List (List (Fin S × Bool)) //
      (∀ l ∈ C, l ≠ []) ∧ C.flatten.length = S} ≤ (4*S)^S := by
  have h := nonemptyChunk_count_le (A := Fin S × Bool) S
  have he : 2*(S*2) = 4*S := by omega
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,he] using h

#print axioms nonemptyChunk_count_le
#print axioms rearrangementShape_count_le
end SpectralRadiusUpperTail
