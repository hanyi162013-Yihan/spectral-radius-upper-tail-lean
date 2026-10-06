import SpectralRadiusUpperTail.SchurNoncommDuhamel
import Mathlib.Data.Matrix.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Entrywise first-upper-edge expansion of a block upper-triangular
matrix power. Matrix entries may themselves be noncommutative matrices. -/
theorem diagonal_plus_upper_power_entry {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (k : ℕ) (i j : ι) :
    ((Matrix.diagonal D + U)^k) i j =
      (if i = j then (D i)^k else 0) +
      ∑ s ∈ Finset.range k, ∑ h : ι,
        (D i)^s * U i h * ((Matrix.diagonal D + U)^(k-s-1)) h j := by
  rw [noncomm_pow_add_duhamel]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.diagonal_pow]
  rw [Matrix.diagonal_apply]
  apply congrArg (fun x : R => (if i = j then (D i)^k else 0) + x)
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_pow, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_assoc]

#print axioms diagonal_plus_upper_power_entry
end SpectralRadiusUpperTail
