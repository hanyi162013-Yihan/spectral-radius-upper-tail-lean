import SpectralRadiusUpperTail.SignedBlockMatchingCount

namespace SpectralRadiusUpperTail
open scoped BigOperators

abbrev VaryingBlockClosingMatching {n : ℕ} {β : Type*} (l : β → ℕ)
    (v : (b : β) → Fin (l b) → Fin n) :=
  {f : NoncrossingMatching n // ∀ b, IsLowerSet {i : Fin (l b) | f.val (v b i) < v b i}}

noncomputable def varyingBlockMatchingCode {n : ℕ} {β : Type*} (l : β → ℕ)
    (v : (b : β) → Fin (l b) → Fin n) (f : VaryingBlockClosingMatching l v) :
    (b : β) → Fin (l b+1) := by
  classical
  exact fun b => initialSegmentCode
    ⟨Finset.univ.filter (fun i => f.val.val (v b i) < v b i), by simpa using f.property b⟩

lemma varyingBlockMatchingCode_injective {n : ℕ} {β : Type*} (l : β → ℕ)
    (v : (b : β) → Fin (l b) → Fin n) (hcover : ∀ i, ∃ b j, v b j = i) :
    Function.Injective (varyingBlockMatchingCode l v) := by
  classical
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply noncrossing_matching_eq_of_openings f.val.val g.val.val
    f.val.property.1 g.val.property.1 f.val.property.2.1 g.val.property.2.1
    f.val.property.2.2 g.val.property.2.2
  intro i
  obtain ⟨b,j,hj⟩ := hcover i
  have he := congrFun h b
  have hs := initialSegmentCode_injective (l b) he
  have ht := congrArg Subtype.val hs
  have hm : (f.val.val (v b j) < v b j) ↔ (g.val.val (v b j) < v b j) := by
    have hh := Finset.ext_iff.mp ht j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hh
  rw [hj] at hm
  have hnf := f.val.property.2.1 i
  have hng := g.val.property.2.1 i
  omega

lemma varyingBlockClosingMatching_count_le {n : ℕ} {β : Type*} [Fintype β]
    (l : β → ℕ) (v : (b : β) → Fin (l b) → Fin n)
    (hcover : ∀ i, ∃ b j, v b j = i) :
    Nat.card (VaryingBlockClosingMatching l v) ≤ ∏ b, (l b+1) := by
  classical
  letI : Fintype (NoncrossingMatching n) := by unfold NoncrossingMatching; infer_instance
  letI : Fintype (VaryingBlockClosingMatching l v) := by
    unfold VaryingBlockClosingMatching; infer_instance
  simpa only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_fin] using
    Fintype.card_le_of_injective (varyingBlockMatchingCode l v)
      (varyingBlockMatchingCode_injective l v hcover)

/-- The product bound survives nonuniform block lengths, including empty blocks.
This permits constant-sign blocks cut apart during a defect encoding. -/
lemma varyingSignBlock_matching_count_le {n : ℕ} {β : Type*} [Fintype β]
    (s : Fin n → Bool) (l : β → ℕ) (v : (b : β) → Fin (l b) → Fin n)
    (hcover : ∀ i, ∃ b j, v b j = i) (hv : ∀ b, StrictMono (v b))
    (hconv : ∀ b i j t, v b i ≤ t → t ≤ v b j → ∃ k, v b k = t)
    (hs : ∀ b i j, s (v b i) = s (v b j)) :
    Nat.card (SignedNoncrossingMatching s) ≤ ∏ b, (l b+1) := by
  classical
  let lift : SignedNoncrossingMatching s → VaryingBlockClosingMatching l v := fun f =>
    ⟨f.val, fun b => convexSignBlock_closings_lower f.val.val s f.val.property.1
      f.property f.val.property.2.2 (v b) (hv b) (hconv b) (hs b)⟩
  have hi : Function.Injective lift := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun x : VaryingBlockClosingMatching l v => x.val) h
  letI : Fintype (NoncrossingMatching n) := by unfold NoncrossingMatching; infer_instance
  letI : Fintype (SignedNoncrossingMatching s) := by unfold SignedNoncrossingMatching; infer_instance
  letI : Fintype (VaryingBlockClosingMatching l v) := by
    unfold VaryingBlockClosingMatching; infer_instance
  have hc : Nat.card (SignedNoncrossingMatching s) ≤
      Nat.card (VaryingBlockClosingMatching l v) := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective lift hi
  exact hc.trans (varyingBlockClosingMatching_count_le l v hcover)

#print axioms VaryingBlockClosingMatching
#print axioms varyingBlockMatchingCode
#print axioms varyingBlockMatchingCode_injective
#print axioms varyingBlockClosingMatching_count_le
#print axioms varyingSignBlock_matching_count_le
end SpectralRadiusUpperTail
