import SpectralRadiusUpperTail.SchurEdgeComponentEntry
import SpectralRadiusUpperTail.SchurEdgeComponentTruncate
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The exact contribution of paths with `l` upper edges, recursively
classified by their first upper edge and its preceding wait. -/
noncomputable def schurFixedEdgeRecursive {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) : ℕ → ℕ → ι → ι → R
  | 0, k, i, j => if i = j then (D i)^k else 0
  | l+1, k, i, j =>
      ∑ s ∈ Finset.range (k-l), ∑ h : ι,
        (D i)^s * U i h * schurFixedEdgeRecursive D U l (k-s-1) h j

theorem schurFixedEdgeRecursive_eq_component {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (l k : ℕ) (hlk : l ≤ k)
    (i j : ι) :
    schurFixedEdgeRecursive D U l k i j =
      (noncommEdgeComponent (Matrix.diagonal D) U l k) i j := by
  induction l generalizing k i j with
  | zero =>
    exact (matrix_edge_component_zero_entry D U k i j).symm
  | succ l ih =>
    have hlt : l < k := by omega
    rw [schurFixedEdgeRecursive,
      noncommEdgeComponent_succ_truncate _ _ l k hlt, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro h _
    have htail : l ≤ k-s-1 := by
      have hs' := Finset.mem_range.mp hs
      omega
    rw [ih (k-s-1) htail h j]
    simp only [Matrix.diagonal_pow, Matrix.diagonal_mul, Pi.pow_apply]

#print axioms schurFixedEdgeRecursive_eq_component
end SpectralRadiusUpperTail
