import SpectralRadiusUpperTail.LogPositiveStability
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma finite_log_product_difference_bound {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (C : ℝ) (h : ∀ i, |Real.log (a i)-Real.log (b i)| ≤ C) :
    |Real.log (∏ i, a i)-Real.log (∏ i, b i)| ≤ (Fintype.card ι : ℝ)*C := by
  rw [Real.log_prod (fun i _ => (ha i).ne'),Real.log_prod (fun i _ => (hb i).ne'),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Real.log (a i)-Real.log (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

#print axioms finite_log_product_difference_bound
end SpectralRadiusUpperTail
