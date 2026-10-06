import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma defect_weight_geometric (n A B : ℝ) (hn : 0 < n) (r g : ℕ) (hg : g ≤ r+1) :
    B^g * (n^(r+1-g) * A^(6*g)) = n^(r+1) * (B*A^6/n)^g := by
  rw [div_pow,mul_pow, ← pow_mul]
  have he : n^(r+1) = n^(r+1-g)*n^g := by
    rw [← pow_add,Nat.sub_add_cancel hg]
  rw [he]
  field_simp
  <;> ring

lemma finite_geometric_sum_le_two (x : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1/2) (r : ℕ) :
    ∑ g : Fin (r+1), x^g.val ≤ 2 := by
  have hbound (k : ℕ) : ∑ i ∈ Finset.range k, x^i ≤ 2*(1-x^k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,pow_succ]
      have hp : 0 ≤ x^k := pow_nonneg hx k
      nlinarith
  have hh := hbound (r+1)
  rw [← Fin.sum_univ_eq_sum_range] at hh
  have hp : 0 ≤ x^(r+1) := pow_nonneg hx _
  linarith

#print axioms defect_weight_geometric
#print axioms finite_geometric_sum_le_two
end SpectralRadiusUpperTail
