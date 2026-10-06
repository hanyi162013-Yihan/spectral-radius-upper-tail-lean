import SpectralRadiusUpperTail.PositionArrangementCode
import SpectralRadiusUpperTail.MarkedChunkEncoding
import SpectralRadiusUpperTail.BoundedFinsetCount

namespace SpectralRadiusUpperTail
variable {L S : ℕ}

lemma PositionArrangementCode.ext_data {C D : PositionArrangementCode L S}
    (hd : C.deleted = D.deleted) (hl : C.lengths = D.lengths) (hr : C.routes = D.routes) :
    C = D := by
  cases C
  cases D
  simp only at hd hl hr
  subst hd
  subst hl
  subst hr
  rfl

/-- Deletions, bounded segment lengths, reversal bits, segment ordering and
route separators together have polynomial cost with exponent O(b+S). -/
lemma positionArrangement_count_le (L S b : ℕ) :
    Nat.card {C : PositionArrangementCode L S // C.deleted.card ≤ b} ≤
      ((b+1)*(max 1 L)^b) * ((L+1)^S * (4*S)^S) := by
  classical
  let P := {C : PositionArrangementCode L S // C.deleted.card ≤ b}
  let encode : P → {D : Finset (Fin L) // D.card ≤ b} ×
      (Fin S → Fin (L+1)) × NonemptyChunks (Fin S × Bool) S := fun C =>
    (⟨C.val.deleted,C.property⟩,C.val.lengths,⟨C.val.routes,C.val.nonempty,C.val.total⟩)
  have hinj : Function.Injective encode := by
    intro C D h
    apply Subtype.ext
    apply PositionArrangementCode.ext_data
    · exact congrArg (fun z => z.1.val) h
    · exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.2.2.val) h
  have h := Nat.card_le_card_of_injective encode hinj
  rw [Nat.card_prod,Nat.card_prod] at h
  have hfun : Nat.card (Fin S → Fin (L+1)) = (L+1)^S := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin]
  rw [hfun] at h
  have hd : Nat.card {D : Finset (Fin L) // D.card ≤ b} ≤ (b+1)*(max 1 L)^b := by
    simpa only [Fintype.card_fin] using (bounded_card_finset_count (A := Fin L) b)
  exact h.trans (Nat.mul_le_mul hd
    (Nat.mul_le_mul_left _ (rearrangementShape_count_le S)))

#print axioms PositionArrangementCode.ext_data
#print axioms positionArrangement_count_le
end SpectralRadiusUpperTail
