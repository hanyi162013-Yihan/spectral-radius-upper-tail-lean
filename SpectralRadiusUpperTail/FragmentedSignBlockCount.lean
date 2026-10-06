import SpectralRadiusUpperTail.FragmentProductBudget
import SpectralRadiusUpperTail.VaryingBlockMatchingCount
import SpectralRadiusUpperTail.ConcatenateSignedMatchings
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma fragment_indexed_product_le {B : Type*} [Fintype B]
    (k : B → ℕ) (l : ∀ b, Fin (k b) → ℕ) (m L K : ℕ) (hmL : m ≤ L)
    (hm : ∀ b j, l b j ≤ m) (hcuts : (∑ b, (k b-1)) ≤ K) :
    (∏ b, ∏ j, (l b j+1)) ≤ (m+1)^Fintype.card B * (L+1)^K := by
  have h := fragment_family_product_le (fun b => List.ofFn (l b)) m L K hmL
    (fun b a ha => by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact hm b j) (by simpa only [List.length_ofFn] using hcuts)
  simpa only [List.map_ofFn,List.prod_ofFn,Function.comp_def] using h

/-- A proved extra-fragment budget preserves the sharp original-block base.
The hypotheses describe actual covering convex constant-sign intervals. -/
lemma fragmentedSignBlock_matching_count_le {n : ℕ} {B : Type*} [Fintype B]
    (s : Fin n → Bool) (k : B → ℕ) (l : ∀ b, Fin (k b) → ℕ)
    (v : (a : Σ b, Fin (k b)) → Fin (l a.1 a.2) → Fin n)
    (hcover : ∀ i, ∃ a j, v a j = i) (hv : ∀ a, StrictMono (v a))
    (hconv : ∀ a i j t, v a i ≤ t → t ≤ v a j → ∃ u, v a u = t)
    (hs : ∀ a i j, s (v a i) = s (v a j))
    (m L K : ℕ) (hmL : m ≤ L) (hm : ∀ b j, l b j ≤ m)
    (hcuts : (∑ b, (k b-1)) ≤ K) :
    Nat.card (SignedNoncrossingMatching s) ≤ (m+1)^Fintype.card B * (L+1)^K := by
  have h := varyingSignBlock_matching_count_le s (fun a : Σ b, Fin (k b) => l a.1 a.2)
    v hcover hv hconv hs
  rw [Fintype.prod_sigma] at h
  exact h.trans (fragment_indexed_product_le k l m L K hmL hm hcuts)

/-- Concatenating a whole family of tour matchings has the same sharp block
base, once its actual fragment intervals and budget have been supplied. -/
lemma tourFamily_fragmented_matching_count_le (W : List FiniteSignWord)
    {B : Type*} [Fintype B] (k : B → ℕ) (l : ∀ b, Fin (k b) → ℕ)
    (v : (a : Σ b, Fin (k b)) → Fin (l a.1 a.2) → Fin (signWordLength W))
    (hcover : ∀ i, ∃ a j, v a j = i) (hv : ∀ a, StrictMono (v a))
    (hconv : ∀ a i j t, v a i ≤ t → t ≤ v a j → ∃ u, v a u = t)
    (hs : ∀ a i j, concatenateSigns W (v a i) = concatenateSigns W (v a j))
    (m L K : ℕ) (hmL : m ≤ L) (hm : ∀ b j, l b j ≤ m)
    (hcuts : (∑ b, (k b-1)) ≤ K) :
    (W.map (fun w => Nat.card (SignedNoncrossingMatching w.2))).prod ≤
      (m+1)^Fintype.card B * (L+1)^K :=
  (concatenateSignedMatchings_count_le W).trans
    (fragmentedSignBlock_matching_count_le (concatenateSigns W) k l v hcover hv hconv hs
      m L K hmL hm hcuts)

#print axioms fragment_indexed_product_le
#print axioms fragmentedSignBlock_matching_count_le
#print axioms tourFamily_fragmented_matching_count_le
end SpectralRadiusUpperTail
