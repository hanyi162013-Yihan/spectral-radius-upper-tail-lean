import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

def pairedList {A : Type*} (P : List (A×A)) : List A :=
  P.flatMap fun p => [p.1,p.2]

lemma pairedList_length {A : Type*} (P : List (A×A)) :
    (pairedList P).length = 2*P.length := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [pairedList, List.flatMap_cons] at *; omega

lemma pairedList_prod {A : Type*} [Monoid A] (P : List (A×A)) :
    (pairedList P).prod = (P.map fun p => p.1*p.2).prod := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    change p.1*(p.2*(pairedList P).prod) = (p.1*p.2)*(P.map fun p => p.1*p.2).prod
    rw [ih, mul_assoc]

lemma pairedList_map_prod {A B : Type*} [Monoid B] (f : A → B) (P : List (A×A)) :
    ((pairedList P).map f).prod = (P.map fun p => f p.1*f p.2).prod := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [pairedList, List.flatMap_cons, ih, mul_assoc] at *

lemma exists_pairedList {A : Type*} (n : ℕ) (L : List A) (h : L.length = 2*n) :
    ∃ P : List (A×A), P.length = n ∧ pairedList P = L := by
  induction n generalizing L with
  | zero =>
    have : L = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst L
    exact ⟨[],rfl,rfl⟩
  | succ n ih =>
    cases L with
    | nil => simp at h
    | cons a L =>
      cases L with
      | nil => simp at h; omega
      | cons b L =>
        have hL : L.length = 2*n := by simp only [List.length_cons] at h; omega
        obtain ⟨P,hP,he⟩ := ih L hL
        refine ⟨(a,b)::P, by simp [hP], ?_⟩
        change a::b::pairedList P = a::b::L
        rw [he]

#print axioms exists_pairedList
#print axioms pairedList_prod
end SpectralRadiusUpperTail
