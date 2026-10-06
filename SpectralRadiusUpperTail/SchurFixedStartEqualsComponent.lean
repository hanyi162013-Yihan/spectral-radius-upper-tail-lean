import SpectralRadiusUpperTail.SchurFixedStartZero
import SpectralRadiusUpperTail.SchurFixedStartPathRecursion
import SpectralRadiusUpperTail.SchurStrictUpperSum
import SpectralRadiusUpperTail.SchurFixedEdgeRecursive
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The explicit sum over strict Schur paths and diagonal waiting times
equals the algebraic fixed-edge recursion, provided the bridge matrix is
strictly upper triangular in block index. -/
theorem schurFixedStartPathSum_eq_recursive (d N : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (hU : ∀ i h : Fin N, ¬ i < h → U i h = 0)
    (l k : ℕ) (hlk : l ≤ k) (i j : Fin N) :
    schurFixedStartPathSum d N l k D U i j =
      schurFixedEdgeRecursive D U l k i j := by
  induction l generalizing k i j with
  | zero =>
    simpa only [schurFixedEdgeRecursive] using
      schurFixedStartPathSum_zero d N k D U i j
  | succ l ih =>
    have hlt : l < k := by omega
    calc
      schurFixedStartPathSum d N (l+1) k D U i j =
          ∑ s : Fin (k-l),
            ∑ h : {h : Fin N // i < h},
              (D i)^s.val * U i h.val *
                schurFixedStartPathSum d N l (k-s.val-1) D U h.val j :=
        schurFixedStartPathSum_succ_recursion d N l k hlt D U i j
      _ = ∑ s : Fin (k-l),
            ∑ h : {h : Fin N // i < h},
              (D i)^s.val * U i h.val *
                schurFixedEdgeRecursive D U l (k-s.val-1) h.val j := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro h _
        have htail : l ≤ k-s.val-1 := by have := s.isLt; omega
        rw [ih (k-s.val-1) htail h.val j]
      _ = ∑ s : Fin (k-l),
            ∑ h : Fin N,
              (D i)^s.val * U i h *
                schurFixedEdgeRecursive D U l (k-s.val-1) h j := by
        apply Finset.sum_congr rfl
        intro s _
        exact schur_strict_upper_sum i
          (fun h => (D i)^s.val * U i h *
            schurFixedEdgeRecursive D U l (k-s.val-1) h j)
          (by intro h hnot; rw [hU i h hnot]; simp)
      _ = schurFixedEdgeRecursive D U (l+1) k i j := by
        rw [schurFixedEdgeRecursive, ← Fin.sum_univ_eq_sum_range]

/-- Therefore the same path sum is the corresponding term in the
noncommutative expansion of `(diagonal D + U)^k`. -/
theorem schurFixedStartPathSum_eq_component (d N : ℕ)
    (D : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin N) (Fin N) (Matrix (Fin d) (Fin d) ℝ))
    (hU : ∀ i h : Fin N, ¬ i < h → U i h = 0)
    (l k : ℕ) (hlk : l ≤ k) (i j : Fin N) :
    schurFixedStartPathSum d N l k D U i j =
      (noncommEdgeComponent (Matrix.diagonal D) U l k) i j := by
  rw [schurFixedStartPathSum_eq_recursive d N D U hU l k hlk i j]
  exact schurFixedEdgeRecursive_eq_component D U l k hlk i j

#print axioms schurFixedStartPathSum_eq_recursive
#print axioms schurFixedStartPathSum_eq_component
end SpectralRadiusUpperTail
