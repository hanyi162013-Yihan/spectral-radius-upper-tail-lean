import SpectralRadiusUpperTail.SignRunCount
import Mathlib.Data.Nat.Basic

namespace SpectralRadiusUpperTail
variable {A : Type*} [DecidableEq A]

lemma signRunCount_remove_second (a b : A) (l : List A) :
    signRunCount (a::l) ≤ signRunCount (a::b::l) := by
  cases l with
  | nil => simp only [signRunCount]; split_ifs <;> omega
  | cons c l =>
    by_cases hab : a = b
    · subst b; simp [signRunCount]
    by_cases hbc : b = c
    · subst c; simp [signRunCount]
    by_cases hac : a = c <;> simp [signRunCount,hab,hbc,hac] <;> omega

/-- Deleting arbitrary positions cannot increase the number of constant-label
runs. The stronger head-preserving assertion makes the induction local. -/
lemma signRunCount_sublist_bounds {l k : List A} (h : l.Sublist k) :
    signRunCount l ≤ signRunCount k ∧
      ∀ a, signRunCount (a::l) ≤ signRunCount (a::k) := by
  induction h with
  | slnil => exact ⟨le_rfl,fun _ => le_rfl⟩
  | @cons l k a h ih =>
    exact ⟨Nat.le_trans ih.1 (signRunCount_cons_bounds a k).1,
      fun b => Nat.le_trans (ih.2 b) (signRunCount_remove_second b a k)⟩
  | @cons_cons l k a h ih =>
    refine ⟨ih.2 a,?_⟩
    intro b
    simpa only [signRunCount] using Nat.add_le_add_right (ih.2 a) (if b = a then 0 else 1)

lemma signRunCount_filter_le (l : List A) (p : A → Bool) :
    signRunCount (l.filter p) ≤ signRunCount l :=
  (signRunCount_sublist_bounds (List.filter_sublist (p := p) (l := l))).1

/-- Filter first, then split into ordered chunks: the number of original-label
fragments is bounded by the original runs plus S-1. Labels can be original
sign-block indices, so equal adjacent signs do not erase block identity. -/
lemma filtered_chunk_run_budget (l : List A) (p : A → Bool) (C : List (List A))
    (hflat : C.flatten = l.filter p) (B S : ℕ)
    (hB : signRunCount l ≤ B) (hS : C.length ≤ S) :
    (C.map signRunCount).sum ≤ B+(S-1) := by
  have h := signRunCount_chunks C
  rw [hflat] at h
  exact Nat.le_trans h (Nat.add_le_add (Nat.le_trans (signRunCount_filter_le l p) hB)
    (Nat.sub_le_sub_right hS 1))

#print axioms signRunCount_remove_second
#print axioms signRunCount_sublist_bounds
#print axioms signRunCount_filter_le
#print axioms filtered_chunk_run_budget
end SpectralRadiusUpperTail
