import SpectralRadiusUpperTail.BoundedKernelData
import SpectralRadiusUpperTail.ArrangementCodeFinite
import SpectralRadiusUpperTail.FiniteSigmaBound

namespace SpectralRadiusUpperTail

abbrev SharpOccurrenceFamily {L : ℕ} (rows : List (List (Fin L × Bool))) (H M : ℕ) :=
  {W : OccurrenceFamily L // W.rows = rows ∧ Fintype.card W.VertexSlot ≤ H ∧ W.matchingCard ≤ M}

instance sharpOccurrenceFamily_subsingleton {L H M : ℕ} (rows : List (List (Fin L × Bool))) :
    Subsingleton (SharpOccurrenceFamily rows H M) := by
  constructor
  intro W Z
  exact Subtype.ext (OccurrenceFamily.rows_injective (W.property.1.trans Z.property.1.symm))

/-- Arrange the code fields in the order in which they are counted: the shape
uniquely fixes the occurrence family, then matching and bounded pair records. -/
abbrev SharpArrangementData {L : ℕ} (s : Fin L → Bool) (S d H M e f : ℕ) :=
  Σ A : {A : PositionArrangementCode L S // A.deleted.card ≤ d},
    Σ W : SharpOccurrenceFamily (A.val.decode s) H M, BoundedKernelData W.val e f

lemma sharpArrangementData_count_le {L : ℕ} (s : Fin L → Bool) (S d H M e f : ℕ) :
    Nat.card (SharpArrangementData s S d H M e f) ≤
      (((d+1)*(max 1 L)^d) * ((L+1)^S * (4*S)^S)) *
        (M * (pairRecordCost H e * pairRecordCost (L+1) f)) := by
  have h := finite_sigma_count_le
    (fun A : {A : PositionArrangementCode L S // A.deleted.card ≤ d} =>
      Σ W : SharpOccurrenceFamily (A.val.decode s) H M, BoundedKernelData W.val e f)
    (M * (pairRecordCost H e * pairRecordCost (L+1) f)) (by
      intro A
      apply subsingleton_sigma_count_le
      intro W
      exact boundedKernelData_count_le W.val H M e f W.property.2.1 W.property.2.2)
  exact h.trans (Nat.mul_le_mul_right _ (positionArrangement_count_le L S d))

#print axioms SharpOccurrenceFamily
#print axioms sharpOccurrenceFamily_subsingleton
#print axioms SharpArrangementData
#print axioms sharpArrangementData_count_le
end SpectralRadiusUpperTail
