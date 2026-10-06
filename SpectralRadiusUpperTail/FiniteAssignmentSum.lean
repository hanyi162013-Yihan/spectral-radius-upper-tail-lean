import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]

/-- Summing one marked coordinate leaves all other labels free. -/
lemma assignment_sum_one_coordinate (a : σ) (f : ι → ℝ) :
    (∑ x : σ → ι, f (x a)) =
      (Fintype.card ι : ℝ)^(Fintype.card σ-1) * ∑ i, f i := by
  calc
    (∑ x : σ → ι, f (x a)) =
        ∑ x : ι × ({j : σ // j ≠ a} → ι), f x.1 :=
      (Equiv.funSplitAt a ι).sum_comp (fun x => f x.1)
    _ = (Fintype.card ι : ℝ)^(Fintype.card σ-1) * ∑ i, f i := by
      simp [Fintype.sum_prod_type, Fintype.card_subtype_compl, ← Finset.mul_sum]

/-- Distinct marked coordinates save two free labels. -/
lemma assignment_sum_two_coordinates (a b : σ) (hba : b ≠ a) (f g : ι → ℝ) :
    (∑ x : σ → ι, f (x a)*g (x b)) =
      (Fintype.card ι : ℝ)^(Fintype.card σ-2) * (∑ i, f i) * ∑ i, g i := by
  calc
    (∑ x : σ → ι, f (x a)*g (x b)) =
        ∑ x : ι × ({j : σ // j ≠ a} → ι), f x.1*g (x.2 ⟨b,hba⟩) :=
      (Equiv.funSplitAt a ι).sum_comp (fun x => f x.1*g (x.2 ⟨b,hba⟩))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, assignment_sum_one_coordinate]
      simp only [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Nat.sub_sub]
      rw [← Finset.sum_mul]
      ring

#print axioms assignment_sum_one_coordinate
#print axioms assignment_sum_two_coordinates
end SpectralRadiusUpperTail
