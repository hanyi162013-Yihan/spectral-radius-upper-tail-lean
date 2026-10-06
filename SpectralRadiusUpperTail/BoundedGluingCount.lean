import SpectralRadiusUpperTail.RelativeGluingCode
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Allowing the number of additional pairs to vary up to b costs only the
factor b+1. The max handles an empty slot domain without a positivity assumption. -/
lemma bounded_gluing_pattern_count (Rlocal : A → A → Prop) (b : ℕ) :
    Nat.card {R : Setoid A // ∃ d ≤ b, ∃ code : Fin d → A × A,
      ∀ x y, R x y ↔ Relation.EqvGen
        (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y} ≤
      (b+1)*(max 1 (Fintype.card A))^(2*b) := by
  classical
  let Fixed (d : ℕ) := {R : Setoid A // ∃ code : Fin d → A × A,
    ∀ x y, R x y ↔ Relation.EqvGen (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y}
  let P := {R : Setoid A // ∃ d ≤ b, ∃ code : Fin d → A × A,
    ∀ x y, R x y ↔ Relation.EqvGen (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y}
  let degree (p : P) := Classical.choose p.property
  have hdeg (p : P) : degree p ≤ b := (Classical.choose_spec p.property).1
  let encode : P → Σ d : Fin (b+1), Fixed d.val := fun p =>
    ⟨⟨degree p,Nat.lt_succ_of_le (hdeg p)⟩,⟨p.val,(Classical.choose_spec p.property).2⟩⟩
  have hinj : Function.Injective encode := by
    intro p q h
    exact Subtype.ext (congrArg (fun z : Σ d : Fin (b+1), Fixed d.val => z.2.val) h)
  have hcard : Nat.card P ≤ ∑ d : Fin (b+1), Nat.card (Fixed d.val) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using
      Fintype.card_le_of_injective encode hinj
  calc
    Nat.card P ≤ ∑ d : Fin (b+1), Nat.card (Fixed d.val) := hcard
    _ ≤ ∑ d : Fin (b+1), (Fintype.card A)^(2*d.val) :=
      Finset.sum_le_sum (fun d _ => relative_gluing_pattern_count Rlocal d.val)
    _ ≤ ∑ _d : Fin (b+1), (max 1 (Fintype.card A))^(2*b) := by
      apply Finset.sum_le_sum
      intro d _
      exact (Nat.pow_le_pow_left (le_max_right 1 (Fintype.card A)) _).trans
        (Nat.pow_le_pow_right (le_max_left 1 (Fintype.card A))
          (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ d.isLt)))
    _ = _ := by simp

#print axioms bounded_gluing_pattern_count
end SpectralRadiusUpperTail
