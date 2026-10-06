import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma fin_path_sum_differences (k : ℕ) (f : Fin (k+1) → ℤ) :
    (∑ a : Fin k, (f a.succ - f a.castSucc)) = f (Fin.last k) - f 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ]
    have h := ih (fun a => f a.succ)
    change (∑ a : Fin k, (f a.succ.succ - f a.castSucc.succ)) =
      f (Fin.last k).succ - f (0 : Fin (k+1)).succ at h
    rw [h]
    have hl : Fin.last (k+1) = (Fin.last k).succ := rfl
    rw [hl]
    ring

lemma bool_cut_step (a b : Bool) :
    (if a = false ∧ b = true then (1 : ℤ) else 0) -
      (if a = true ∧ b = false then (1 : ℤ) else 0) =
      (if b then (1 : ℤ) else 0) - (if a then (1 : ℤ) else 0) := by
  cases a <;> cases b <;> decide

/-- A closed path crosses any Boolean cut equally often in each direction. -/
lemma closedPath_cut_crossings_eq (k : ℕ) (b : Fin (k+1) → Bool)
    (hclosed : b (Fin.last k) = b 0) :
    (∑ a : Fin k, if b a.castSucc = false ∧ b a.succ = true then (1 : ℕ) else 0) =
    (∑ a : Fin k, if b a.castSucc = true ∧ b a.succ = false then (1 : ℕ) else 0) := by
  have h := fin_path_sum_differences k (fun a => if b a then (1 : ℤ) else 0)
  rw [hclosed, sub_self] at h
  simp_rw [← bool_cut_step] at h
  rw [Finset.sum_sub_distrib] at h
  have he := sub_eq_zero.mp h
  exact_mod_cast he

#print axioms fin_path_sum_differences
#print axioms bool_cut_step
#print axioms closedPath_cut_crossings_eq
end SpectralRadiusUpperTail
