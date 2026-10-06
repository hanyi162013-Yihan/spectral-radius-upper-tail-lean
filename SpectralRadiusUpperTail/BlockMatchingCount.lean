import SpectralRadiusUpperTail.BlockMatchingCode

namespace SpectralRadiusUpperTail

/-- Covering blocks whose closing positions are initial segments give a uniform
exponential count of actual noncrossing matchings. -/
lemma blockClosingMatching_count_le {n m : ℕ} {β : Type*} [Fintype β]
    (v : β → Fin m → Fin n) (hcover : ∀ i, ∃ b j, v b j = i) :
    Nat.card (BlockClosingMatching v) ≤ (m+1) ^ Fintype.card β := by
  classical
  letI : Fintype (NoncrossingMatching n) := by unfold NoncrossingMatching; infer_instance
  letI : Fintype (BlockClosingMatching v) := by unfold BlockClosingMatching; infer_instance
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective (blockMatchingCode v) (blockMatchingCode_injective v hcover)

#print axioms blockClosingMatching_count_le
end SpectralRadiusUpperTail
