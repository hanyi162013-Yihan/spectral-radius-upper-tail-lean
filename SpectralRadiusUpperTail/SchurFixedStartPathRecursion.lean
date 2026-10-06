import SpectralRadiusUpperTail.SchurFixedStartPathSum
import SpectralRadiusUpperTail.SchurStrictTailFirstVertexSum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The explicit strict-path sum satisfies the first-edge recursion,
with the next vertex still indexed by its strict upper-triangular subtype. -/
theorem schurFixedStartPathSum_succ_recursion (d N l k : ℕ)
    (hlk : l < k)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (i j : Fin N) :
    schurFixedStartPathSum d N (l+1) k D U i j =
      ∑ s : Fin (k-l),
        ∑ h : {h : Fin N // i < h},
          (D i)^s.val * U i h.val *
            schurFixedStartPathSum d N l (k-s.val-1) D U h.val j := by
  rw [schurFixedStartPathSum_succ_reindex d N l k hlk D U i j]
  apply Finset.sum_congr rfl
  intro s _
  rw [schurStrictTailFirstVertex_sum]
  apply Finset.sum_congr rfl
  intro h _
  unfold schurFixedStartPathSum
  rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hj : q.val.val (Fin.last l) = j
  · simp [hj, q.property, mul_assoc]
  · simp [hj]

#print axioms schurFixedStartPathSum_succ_recursion
end SpectralRadiusUpperTail
