import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Group nonzero summands by a bounded defect. No independence assumption is
involved in this finite partition. -/
lemma finite_sum_le_defect_counts {α : Type*} [Fintype α]
    (f : α → ℝ) (d : α → ℕ) (r : ℕ) (B : ℕ → ℝ)
    (hn : ∀ a, 0 ≤ f a) (hd : ∀ a, f a ≠ 0 → d a ≤ r)
    (hb : ∀ a, f a ≠ 0 → f a ≤ B (d a)) :
    ∑ a, f a ≤ ∑ g : Fin (r+1),
      (Nat.card {a : α // f a ≠ 0 ∧ d a = g.val} : ℝ) * B g.val := by
  classical
  let S := {a : α // f a ≠ 0}
  let D : S → Fin (r+1) := fun a => ⟨d a.val, Nat.lt_succ_of_le (hd a.val a.property)⟩
  have he : (∑ a : α, f a) = ∑ a : S, f a.val := by
    symm
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => f a ≠ 0)) (by intro a; simp) f]
    exact Finset.sum_filter_of_ne (by intro a h; simpa using h)
  rw [he]
  have hp := (Equiv.sigmaFiberEquiv D).sum_comp (fun a => f a.val)
  rw [← hp, Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro g _
  have hc : Nat.card {a : S // D a = g} =
      Nat.card {a : α // f a ≠ 0 ∧ d a = g.val} := by
    apply Nat.card_congr
    exact {
      toFun := fun a => ⟨a.val.val,a.val.property,congrArg Fin.val a.property⟩
      invFun := fun a => ⟨⟨a.val,a.property.1⟩,Fin.ext a.property.2⟩
      left_inv := fun a => by cases a; rfl
      right_inv := fun a => by cases a; rfl }
  calc
    _ ≤ ∑ a : {a : S // D a = g}, B g.val := by
      apply Finset.sum_le_sum
      intro a _
      have hh := hb a.val.val a.val.property
      have hhg : d a.val.val = g.val := congrArg Fin.val a.property
      simpa only [Equiv.sigmaFiberEquiv_apply,hhg] using hh
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul,
      ← Nat.card_eq_fintype_card,hc,Nat.cast_mul]

#print axioms finite_sum_le_defect_counts
end SpectralRadiusUpperTail
