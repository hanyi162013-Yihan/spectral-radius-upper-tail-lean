import SpectralRadiusUpperTail.FiniteEqualityPatterns
import SpectralRadiusUpperTail.EqualityPatternEquiv
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

noncomputable def equalityPatternContribution (r : Setoid α) (F : (α → β) → ℝ) : ℝ := by
  classical
  exact ∑ f : {f : Quotient r → β // Function.Injective f},
    F (fun a => f.1 (Quotient.mk r a))

/-- Exact partition of a finite assignment sum by equality patterns, with
 each pattern parametrized by injective quotient assignments. -/
lemma sum_eq_equalityPatterns (F : (α → β) → ℝ) :
    (∑ x : α → β, F x) = ∑ r : Setoid α, equalityPatternContribution r F := by
  classical
  calc
    (∑ x : α → β, F x) =
        ∑ r : Setoid α, ∑ x : {x : α → β // Setoid.ker x = r}, F x.1 := by
      simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
        ((Equiv.sigmaFiberEquiv (fun x : α → β => Setoid.ker x)).sum_comp F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact (equalityPatternEquiv r).sum_comp
        (fun f => F (fun a => f.1 (Quotient.mk r a)))

/-- For nonnegative summands, injective quotient assignments may be
 enlarged to all assignments, making endpoint estimates applicable. -/
lemma equalityPatternContribution_le (r : Setoid α) [DecidableRel r.r]
    (F : (α → β) → ℝ) (hF : ∀ x, 0 ≤ F x) :
    equalityPatternContribution r F ≤
      ∑ f : Quotient r → β, F (fun a => f (Quotient.mk r a)) := by
  classical
  unfold equalityPatternContribution
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun f : Quotient r → β => Function.Injective f))
    (by intro f; simp) (fun f => F (fun a => f (Quotient.mk r a)))]
  exact Finset.sum_le_univ_sum_of_nonneg (fun f => hF _)

#print axioms equalityPatternContribution
#print axioms sum_eq_equalityPatterns
#print axioms equalityPatternContribution_le
end SpectralRadiusUpperTail
