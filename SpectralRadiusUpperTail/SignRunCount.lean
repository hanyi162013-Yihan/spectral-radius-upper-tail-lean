import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

namespace SpectralRadiusUpperTail
variable {A : Type*} [DecidableEq A]

/-- Number of maximal constant-label runs, retaining original block labels
rather than merging fragments merely because their signs coincide. -/
def signRunCount : List A → ℕ
  | [] => 0
  | [_] => 1
  | a :: b :: l => signRunCount (b :: l) + if a = b then 0 else 1

lemma signRunCount_cons_bounds (a : A) (l : List A) :
    signRunCount l ≤ signRunCount (a::l) ∧
      signRunCount (a::l) ≤ signRunCount l+1 := by
  cases l with
  | nil => simp [signRunCount]
  | cons b l =>
    rw [signRunCount]
    split_ifs <;> omega

/-- Cutting at one boundary increases the total run count by at most one. -/
lemma signRunCount_append (l k : List A) :
    signRunCount l + signRunCount k ≤ signRunCount (l++k)+1 := by
  induction l with
  | nil => simp [signRunCount]
  | cons a l ih =>
    cases l with
    | nil =>
      have h := (signRunCount_cons_bounds a k).1
      simp only [signRunCount,List.singleton_append]
      omega
    | cons b l =>
      simp only [List.cons_append,signRunCount] at ih ⊢
      split_ifs <;> omega

/-- Arbitrary ordered cuts into S chunks add at most S-1 runs. Empty chunks
are allowed. Reordering/reversal can subsequently preserve these fragment IDs. -/
lemma signRunCount_chunks (C : List (List A)) :
    (C.map signRunCount).sum ≤ signRunCount C.flatten + (C.length-1) := by
  induction C with
  | nil => simp [signRunCount]
  | cons l C ih =>
    cases C with
    | nil => simp
    | cons k C =>
      have h := signRunCount_append l (k::C).flatten
      simp only [List.map_cons,List.sum_cons,List.length_cons,List.flatten_cons] at ih h ⊢
      omega

#print axioms signRunCount
#print axioms signRunCount_cons_bounds
#print axioms signRunCount_append
#print axioms signRunCount_chunks
end SpectralRadiusUpperTail
