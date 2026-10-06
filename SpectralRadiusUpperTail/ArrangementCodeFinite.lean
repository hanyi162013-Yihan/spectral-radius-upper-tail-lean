import SpectralRadiusUpperTail.ArrangementKernelCode
import SpectralRadiusUpperTail.PositionArrangementCount

namespace SpectralRadiusUpperTail
variable {L S : ℕ} {s : Fin L → Bool}

instance positionArrangementCode_finite : Finite (PositionArrangementCode L S) := by
  let encode : PositionArrangementCode L S → Finset (Fin L) ×
      (Fin S → Fin (L+1)) × NonemptyChunks (Fin S × Bool) S := fun C =>
    (C.deleted,C.lengths,⟨C.routes,C.nonempty,C.total⟩)
  apply Finite.of_injective encode
  intro C D h
  exact PositionArrangementCode.ext_data
    (congrArg (fun z => z.1) h) (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2.val) h)

instance occurrenceFamily_rows_subsingleton (rows : List (List (Fin L × Bool))) :
    Subsingleton {W : OccurrenceFamily L // W.rows = rows} := by
  constructor
  intro W Z
  exact Subtype.ext (OccurrenceFamily.rows_injective (W.property.trans Z.property.symm))

abbrev KernelData (W : OccurrenceFamily L) :=
  (∀ i : Fin W.count, SignedNoncrossingMatching (fun j => (W.words i j).2)) ×
    Finset (W.VertexSlot × W.VertexSlot) × Finset (Fin (L+1) × Fin (L+1))

abbrev ArrangementKernelData (s : Fin L → Bool) (S : ℕ) :=
  Σ A : PositionArrangementCode L S, Σ W : {W : OccurrenceFamily L // W.rows = A.decode s},
    KernelData W.val

def ArrangementKernelCode.toData (C : ArrangementKernelCode s S) : ArrangementKernelData s S :=
  ⟨C.arrangement,⟨C.kernel.family,C.rows_eq⟩,C.kernel.matchings,C.kernel.gluing,C.kernel.restoration⟩

def ArrangementKernelCode.ofData (D : ArrangementKernelData s S) : ArrangementKernelCode s S :=
  ⟨D.1,⟨D.2.1.val,D.2.2.1,D.2.2.2.1,D.2.2.2.2⟩,D.2.1.property⟩

lemma ArrangementKernelCode.ofData_toData (C : ArrangementKernelCode s S) :
    ArrangementKernelCode.ofData C.toData = C := by cases C; rfl

instance arrangementKernelCode_finite : Finite (ArrangementKernelCode s S) := by
  apply Finite.of_injective ArrangementKernelCode.toData
  exact Function.LeftInverse.injective ArrangementKernelCode.ofData_toData

#print axioms positionArrangementCode_finite
#print axioms occurrenceFamily_rows_subsingleton
#print axioms KernelData
#print axioms ArrangementKernelData
#print axioms ArrangementKernelCode.toData
#print axioms ArrangementKernelCode.ofData
#print axioms ArrangementKernelCode.ofData_toData
#print axioms arrangementKernelCode_finite
end SpectralRadiusUpperTail
