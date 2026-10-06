import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- First-off-diagonal expansion, valid without commuting the diagonal
and upper-triangular pieces. -/
theorem noncomm_pow_add_duhamel {R : Type*} [Semiring R] (D U : R) (k : ℕ) :
    (D+U)^k = D^k + ∑ s ∈ Finset.range k, D^s * U * (D+U)^(k-s-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', add_mul]
    nth_rewrite 1 [ih]
    rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, tsub_zero]
    have hsum :
        (∑ i ∈ Finset.range k, D * (D^i * U * (D+U)^(k-i-1))) =
          ∑ i ∈ Finset.range k, D^(i+1) * U * (D+U)^(k+1-(i+1)-1) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : k+1-(i+1)-1 = k-i-1 := by omega
      rw [he]
      simp only [← mul_assoc, ← pow_succ']
    rw [hsum, ← pow_succ' D k]
    have he : k+1-1 = k := by omega
    rw [he]
    exact add_assoc _ _ _

#print axioms noncomm_pow_add_duhamel
end SpectralRadiusUpperTail
