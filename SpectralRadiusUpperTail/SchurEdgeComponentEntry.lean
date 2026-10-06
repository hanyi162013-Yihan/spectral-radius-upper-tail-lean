import SpectralRadiusUpperTail.SchurEdgeComponents
import Mathlib.Data.Matrix.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The zero-edge component stays in one diagonal block. -/
theorem matrix_edge_component_zero_entry {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (k : ℕ) (i j : ι) :
    (noncommEdgeComponent (Matrix.diagonal D) U 0 k) i j =
      if i = j then (D i)^k else 0 := by
  simp only [noncommEdgeComponent, Matrix.diagonal_pow, Matrix.diagonal_apply, Pi.pow_apply]

/-- The first of exactly `l+1` upper edges follows `s` diagonal steps.
This is the entrywise recursion that the strict-path expansion must satisfy. -/
theorem matrix_edge_component_succ_entry {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (l k : ℕ) (i j : ι) :
    (noncommEdgeComponent (Matrix.diagonal D) U (l+1) k) i j =
      ∑ s ∈ Finset.range k, ∑ h : ι,
        (D i)^s * U i h *
          (noncommEdgeComponent (Matrix.diagonal D) U l (k-s-1)) h j := by
  rw [noncommEdgeComponent]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply]

#print axioms matrix_edge_component_zero_entry
#print axioms matrix_edge_component_succ_entry
end SpectralRadiusUpperTail
