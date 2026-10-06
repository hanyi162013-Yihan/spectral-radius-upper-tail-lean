import SpectralRadiusUpperTail.OccurrenceMatchingCard
import SpectralRadiusUpperTail.PairRecordCount

namespace SpectralRadiusUpperTail

abbrev BoundedKernelData {L : ℕ} (W : OccurrenceFamily L) (e f : ℕ) :=
  W.Matchings × {E : Finset (W.VertexSlot × W.VertexSlot) // E.card ≤ e} ×
    {F : Finset (Fin (L+1) × Fin (L+1)) // F.card ≤ f}

lemma boundedKernelData_count_le {L : ℕ} (W : OccurrenceFamily L) (H M e f : ℕ)
    (hH : Fintype.card W.VertexSlot ≤ H) (hM : W.matchingCard ≤ M) :
    Nat.card (BoundedKernelData W e f) ≤ M * (pairRecordCost H e * pairRecordCost (L+1) f) := by
  classical
  change Nat.card (W.Matchings × {E : Finset (W.VertexSlot × W.VertexSlot) // E.card ≤ e} ×
    {F : Finset (Fin (L+1) × Fin (L+1)) // F.card ≤ f}) ≤ _
  rw [Nat.card_prod,Nat.card_prod]
  exact Nat.mul_le_mul hM (Nat.mul_le_mul (bounded_pair_record_count H e hH)
    (bounded_pair_record_count (L+1) f (by simp)))

#print axioms BoundedKernelData
#print axioms boundedKernelData_count_le
end SpectralRadiusUpperTail
