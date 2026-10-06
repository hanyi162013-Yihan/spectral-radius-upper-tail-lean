import SpectralRadiusUpperTail.SignedMultiplicityCount
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace SpectralRadiusUpperTail
variable {σ : Type*} [DecidableEq σ] [BEq σ] [LawfulBEq σ]

lemma list_count_indicator_sum (L : List σ) (j : σ) :
    L.count j = (L.map (fun i => if i = j then 1 else 0)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    by_cases hi : i = j
    · subst i; simp [ih,Nat.add_comm]
    · simp [ih,hi,Ne.symm hi]

lemma list_ofFn_entryMultiplicity [Fintype σ] {n : ℕ} (e : Fin n → σ) (j : σ) :
    (List.ofFn e).count j = entryMultiplicity e j := by
  rw [list_count_indicator_sum,entryMultiplicity_indicator_sum]
  simp [List.map_ofFn,List.sum_ofFn,Function.comp_def]

lemma list_filter_count (L : List σ) (P : σ → Bool) (j : σ) :
    (L.filter P).count j = if P j then L.count j else 0 := by
  cases hj : P j with
  | false =>
    rw [if_neg (by simp [hj])]
    apply List.count_eq_zero.mpr
    simp [hj]
  | true => simpa [hj] using (List.count_filter (l := L) (a := j) hj)

lemma list_filter_length_indicator {α : Type*} (L : List α) (P : α → Bool) :
    (L.filter P).length = (L.map (fun i => if P i then 1 else 0)).sum := by
  induction L with
  | nil => simp
  | cons i L ih => cases hi : P i <;> simp [hi,ih,Nat.add_comm]

lemma list_ofFn_filter_length {α : Type*} {n : ℕ} (e : Fin n → α) (P : α → Bool) :
    ((List.ofFn e).filter P).length = (Finset.univ.filter (fun i => P (e i))).card := by
  classical
  rw [list_filter_length_indicator]
  simp only [List.map_ofFn,List.sum_ofFn,Finset.card_eq_sum_ones,Finset.sum_filter,Function.comp_def]

#print axioms list_count_indicator_sum
#print axioms list_ofFn_entryMultiplicity
#print axioms list_filter_count
#print axioms list_filter_length_indicator
#print axioms list_ofFn_filter_length
end SpectralRadiusUpperTail
