import SpectralRadiusUpperTail.SharpArrangementCode
import SpectralRadiusUpperTail.OccurrenceSlotBudget

namespace SpectralRadiusUpperTail
variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
variable {s : Fin (2*r) → Bool} {v : Fin (2*r+1) → V}

lemma DefectRouteCertificate.exists_sharp_arrangement_code (c : DefectRouteCertificate s v)
    (M : ℕ) (hM : c.occurrenceFamily.matchingCard ≤ M) :
    ∃ C : SharpArrangementCode s c.segments.length (8*(r+1-Fintype.card V))
      (4*r) M (8*(r+1-Fintype.card V)) (8*(r+1-Fintype.card V)+1),
      C.val.decode = Setoid.ker v := by
  obtain ⟨K,hK,hdec,hE,hF⟩ := c.exists_kernel_code
  have hrows : K.family.rows = c.positionArrangementCode.decode s := by
    rw [hK,c.occurrenceFamily_rows,c.positionArrangementCode_decode]
  let C : ArrangementKernelCode s c.segments.length := ⟨c.positionArrangementCode,K,hrows⟩
  refine ⟨⟨C,c.deletion_budget,?_,?_,hE,hF⟩,hdec⟩
  · change Fintype.card K.family.VertexSlot ≤ 4*r
    rw [hK]
    exact c.occurrenceFamily_slot_budget
  · change K.family.matchingCard ≤ M
    rw [hK]
    exact hM

#print axioms DefectRouteCertificate.exists_sharp_arrangement_code
end SpectralRadiusUpperTail
