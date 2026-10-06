import SpectralRadiusUpperTail.BlockMatchingCount
import SpectralRadiusUpperTail.ConvexSignBlock
import SpectralRadiusUpperTail.UniformBlockIndex

namespace SpectralRadiusUpperTail

abbrev SignedNoncrossingMatching {n : ℕ} (s : Fin n → Bool) :=
  {f : NoncrossingMatching n // ∀ i, s (f.val i) ≠ s i}

lemma signedNoncrossingMatching_count_le {n m : ℕ} {β : Type*} [Fintype β]
    (s : Fin n → Bool) (v : β → Fin m → Fin n)
    (hcover : ∀ i, ∃ b j, v b j = i) (hv : ∀ b, StrictMono (v b))
    (hconv : ∀ b i j t, v b i ≤ t → t ≤ v b j → ∃ k, v b k = t)
    (hs : ∀ b i j, s (v b i) = s (v b j)) :
    Nat.card (SignedNoncrossingMatching s) ≤ (m+1) ^ Fintype.card β := by
  classical
  let lift : SignedNoncrossingMatching s → BlockClosingMatching v := fun f =>
    ⟨f.val, fun b => convexSignBlock_closings_lower f.val.val s f.val.property.1
      f.property f.val.property.2.2 (v b) (hv b) (hconv b) (hs b)⟩
  have hi : Function.Injective lift := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun x : BlockClosingMatching v => x.val) h
  letI : Fintype (NoncrossingMatching n) := by unfold NoncrossingMatching; infer_instance
  letI : Fintype (SignedNoncrossingMatching s) := by unfold SignedNoncrossingMatching; infer_instance
  letI : Fintype (BlockClosingMatching v) := by unfold BlockClosingMatching; infer_instance
  have hc : Nat.card (SignedNoncrossingMatching s) ≤ Nat.card (BlockClosingMatching v) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective lift hi
  exact hc.trans (blockClosingMatching_count_le v hcover)

/-- B constant-sign blocks of length m admit at most (m+1)^B noncrossing
opposite-sign perfect matchings. -/
lemma uniformSignBlock_matching_count_le (B m : ℕ) (s : Fin (B*m) → Bool)
    (hs : ∀ b : Fin B, ∀ i j : Fin m,
      s (uniformBlockIndex b i) = s (uniformBlockIndex b j)) :
    Nat.card (SignedNoncrossingMatching s) ≤ (m+1)^B := by
  simpa only [Fintype.card_fin] using
    signedNoncrossingMatching_count_le s (@uniformBlockIndex B m)
      (uniformBlockIndex_cover B m) (fun b => uniformBlockIndex_strictMono b)
      (fun b i j t => uniformBlockIndex_convex b i j t) hs

#print axioms SignedNoncrossingMatching
#print axioms signedNoncrossingMatching_count_le
#print axioms uniformSignBlock_matching_count_le
end SpectralRadiusUpperTail
