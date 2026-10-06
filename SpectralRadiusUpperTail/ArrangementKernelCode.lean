import SpectralRadiusUpperTail.DefectKernelCode
import SpectralRadiusUpperTail.PositionArrangementCode
import SpectralRadiusUpperTail.OccurrenceSlotBudget

namespace SpectralRadiusUpperTail

/-- Full vertex-free code, with the occurrence family constrained to be the
one decoded by the economical position arrangement. -/
structure ArrangementKernelCode {L : ℕ} (s : Fin L → Bool) (S : ℕ) where
  arrangement : PositionArrangementCode L S
  kernel : OccurrenceKernelCode L
  rows_eq : kernel.family.rows = arrangement.decode s

def ArrangementKernelCode.decode {L S : ℕ} {s : Fin L → Bool}
    (C : ArrangementKernelCode s S) : Setoid (Fin (L+1)) := C.kernel.decode s

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

/-- A genuine defect certificate supplies a fully label-free decoder, with
all deletion, segment, slot, gluing and restoration budgets proved. -/
lemma DefectRouteCertificate.exists_arrangement_kernel_code (c : DefectRouteCertificate s v) :
    ∃ C : ArrangementKernelCode s c.segments.length,
      C.decode = Setoid.ker v ∧
      C.arrangement.deleted.card ≤ 8*(r+1-Fintype.card V) ∧
      Fintype.card C.kernel.family.VertexSlot ≤ 4*r ∧
      C.kernel.gluing.card ≤ 8*(r+1-Fintype.card V) ∧
      C.kernel.restoration.card ≤ 8*(r+1-Fintype.card V)+1 := by
  obtain ⟨K,hK,hdec,hE,hF⟩ := c.exists_kernel_code
  have hrows : K.family.rows = c.positionArrangementCode.decode s := by
    rw [hK,c.occurrenceFamily_rows,c.positionArrangementCode_decode]
  refine ⟨⟨c.positionArrangementCode,K,hrows⟩,hdec,c.deletion_budget,?_,hE,hF⟩
  rw [hK]
  exact c.occurrenceFamily_slot_budget

lemma arrangementKernelCode_same_arrangement_family {L S : ℕ} {s : Fin L → Bool}
    (C D : ArrangementKernelCode s S) (h : C.arrangement = D.arrangement) :
    C.kernel.family = D.kernel.family :=
  OccurrenceFamily.rows_injective (C.rows_eq.trans ((congrArg (PositionArrangementCode.decode s) h).trans
    D.rows_eq.symm))

#print axioms ArrangementKernelCode
#print axioms ArrangementKernelCode.decode
#print axioms DefectRouteCertificate.exists_arrangement_kernel_code
#print axioms arrangementKernelCode_same_arrangement_family
end SpectralRadiusUpperTail
