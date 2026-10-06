import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Basic

namespace SpectralRadiusUpperTail
variable {A B : Type*}

/-- Cut a list deterministically at the prescribed successive lengths. -/
def partitionByLengths : List ℕ → List A → List (List A)
  | [], _ => []
  | n::ns, l => l.take n :: partitionByLengths ns (l.drop n)

lemma partitionByLengths_length (ns : List ℕ) (l : List A) :
    (partitionByLengths ns l).length = ns.length := by
  induction ns generalizing l with
  | nil => rfl
  | cons n ns ih => simp only [partitionByLengths,List.length_cons,ih]

lemma partitionByLengths_map (ns : List ℕ) (l : List A) (f : A → B) :
    (partitionByLengths ns l).map (List.map f) = partitionByLengths ns (l.map f) := by
  induction ns generalizing l with
  | nil => rfl
  | cons n ns ih => simp only [partitionByLengths,List.map_cons,List.map_take,List.map_drop,ih]

lemma partitionByLengths_self (J : List (List A)) :
    partitionByLengths (J.map List.length) J.flatten = J := by
  induction J with
  | nil => rfl
  | cons l J ih =>
    simpa only [List.map_cons,List.flatten_cons,partitionByLengths,List.take_left,List.drop_left,ih]

/-- No information about payload labels is needed to lift an existing
partition: its length list determines the partition of original positions. -/
lemma partitionByLengths_map_eq (l : List A) (f : A → B) (J : List (List B))
    (h : l.map f = J.flatten) :
    (partitionByLengths (J.map List.length) l).map (List.map f) = J := by
  rw [partitionByLengths_map,h,partitionByLengths_self]

lemma partitionByLengths_lengths (ns : List ℕ) (l : List A) (h : ns.sum = l.length) :
    (partitionByLengths ns l).map List.length = ns := by
  induction ns generalizing l with
  | nil => rfl
  | cons n ns ih =>
    have hn : n ≤ l.length := by simpa only [List.sum_cons] using Nat.le_add_right n ns.sum |>.trans_eq h
    have ht : ns.sum = (l.drop n).length := by
      simp only [List.sum_cons] at h
      rw [List.length_drop]
      omega
    simp only [partitionByLengths,List.map_cons,List.length_take, Nat.min_eq_left hn,ih _ ht]

lemma partitionByLengths_flatten (ns : List ℕ) (l : List A) (h : ns.sum = l.length) :
    (partitionByLengths ns l).flatten = l := by
  induction ns generalizing l with
  | nil =>
    have hl : l = [] := List.length_eq_zero_iff.mp h.symm
    subst l
    rfl
  | cons n ns ih =>
    have ht : ns.sum = (l.drop n).length := by
      simp only [List.sum_cons] at h
      rw [List.length_drop]
      omega
    simp only [partitionByLengths,List.flatten_cons,ih _ ht,List.take_append_drop]

#print axioms partitionByLengths
#print axioms partitionByLengths_length
#print axioms partitionByLengths_map
#print axioms partitionByLengths_self
#print axioms partitionByLengths_map_eq
#print axioms partitionByLengths_lengths
#print axioms partitionByLengths_flatten
end SpectralRadiusUpperTail
