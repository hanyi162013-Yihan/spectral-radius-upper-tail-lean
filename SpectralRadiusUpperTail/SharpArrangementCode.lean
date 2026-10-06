import SpectralRadiusUpperTail.SharpArrangementData

namespace SpectralRadiusUpperTail

abbrev SharpArrangementCode {L : ℕ} (s : Fin L → Bool) (S d H M e f : ℕ) :=
  {C : ArrangementKernelCode s S // C.arrangement.deleted.card ≤ d ∧
    Fintype.card C.kernel.family.VertexSlot ≤ H ∧ C.kernel.family.matchingCard ≤ M ∧
    C.kernel.gluing.card ≤ e ∧ C.kernel.restoration.card ≤ f}

def sharpArrangementEncode {L S d H M e f : ℕ} {s : Fin L → Bool}
    (C : SharpArrangementCode s S d H M e f) : SharpArrangementData s S d H M e f :=
  ⟨⟨C.val.arrangement,C.property.1⟩,
    ⟨C.val.kernel.family,C.val.rows_eq,C.property.2.1,C.property.2.2.1⟩,
    C.val.kernel.matchings,⟨C.val.kernel.gluing,C.property.2.2.2.1⟩,
    ⟨C.val.kernel.restoration,C.property.2.2.2.2⟩⟩

def sharpArrangementErase {L S d H M e f : ℕ} {s : Fin L → Bool}
    (D : SharpArrangementData s S d H M e f) : ArrangementKernelCode s S :=
  ⟨D.1.val,⟨D.2.1.val,D.2.2.1,D.2.2.2.1.val,D.2.2.2.2.val⟩,D.2.1.property.1⟩

lemma sharpArrangementEncode_injective {L S d H M e f : ℕ} {s : Fin L → Bool} :
    Function.Injective (@sharpArrangementEncode L S d H M e f s) := by
  intro C D h
  apply Subtype.ext
  exact congrArg sharpArrangementErase h

lemma sharpArrangementCode_count_le {L : ℕ} (s : Fin L → Bool) (S d H M e f : ℕ) :
    Nat.card (SharpArrangementCode s S d H M e f) ≤
      (((d+1)*(max 1 L)^d) * ((L+1)^S * (4*S)^S)) *
        (M * (pairRecordCost H e * pairRecordCost (L+1) f)) :=
  (Nat.card_le_card_of_injective sharpArrangementEncode sharpArrangementEncode_injective).trans
    (sharpArrangementData_count_le s S d H M e f)

#print axioms SharpArrangementCode
#print axioms sharpArrangementEncode
#print axioms sharpArrangementErase
#print axioms sharpArrangementEncode_injective
#print axioms sharpArrangementCode_count_le
end SpectralRadiusUpperTail
