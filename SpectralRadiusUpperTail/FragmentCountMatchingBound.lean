import SpectralRadiusUpperTail.FragmentedSignBlockCount

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- For uniform original block length m, it suffices to bound the TOTAL
number of fragments by B+K. No assignment of a nonempty fragment to every
original block is needed, so entirely deleted blocks cause no difficulty. -/
lemma fragmentCount_matching_count_le {n : ℕ} {β : Type*} [Fintype β]
    (s : Fin n → Bool) (l : β → ℕ) (v : (b : β) → Fin (l b) → Fin n)
    (hcover : ∀ i, ∃ b j, v b j = i) (hv : ∀ b, StrictMono (v b))
    (hconv : ∀ b i j t, v b i ≤ t → t ≤ v b j → ∃ k, v b k = t)
    (hs : ∀ b i j, s (v b i) = s (v b j))
    (m L B K : ℕ) (hmL : m ≤ L) (hm : ∀ b, l b ≤ m)
    (hnum : Fintype.card β ≤ B+K) :
    Nat.card (SignedNoncrossingMatching s) ≤ (m+1)^B * (L+1)^K := by
  classical
  calc
    _ ≤ ∏ b, (l b+1) := varyingSignBlock_matching_count_le s l v hcover hv hconv hs
    _ ≤ ∏ _b : β, (m+1) := Finset.prod_le_prod' (fun b _ => Nat.add_le_add_right (hm b) 1)
    _ = (m+1)^Fintype.card β := by simp
    _ ≤ (m+1)^(B+K) := Nat.pow_le_pow_right (by omega) hnum
    _ = (m+1)^B * (m+1)^K := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hmL 1) K)

lemma tourFamily_fragmentCount_matching_count_le (W : List FiniteSignWord)
    {β : Type*} [Fintype β] (l : β → ℕ)
    (v : (b : β) → Fin (l b) → Fin (signWordLength W))
    (hcover : ∀ i, ∃ b j, v b j = i) (hv : ∀ b, StrictMono (v b))
    (hconv : ∀ b i j t, v b i ≤ t → t ≤ v b j → ∃ k, v b k = t)
    (hs : ∀ b i j, concatenateSigns W (v b i) = concatenateSigns W (v b j))
    (m L B K : ℕ) (hmL : m ≤ L) (hm : ∀ b, l b ≤ m)
    (hnum : Fintype.card β ≤ B+K) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching w.2))).prod ≤ (m+1)^B * (L+1)^K :=
  (concatenateSignedMatchings_count_le W).trans
    (fragmentCount_matching_count_le (concatenateSigns W) l v hcover hv hconv hs m L B K hmL hm hnum)

#print axioms fragmentCount_matching_count_le
#print axioms tourFamily_fragmentCount_matching_count_le
end SpectralRadiusUpperTail
