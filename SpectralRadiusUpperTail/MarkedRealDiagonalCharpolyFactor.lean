import SpectralRadiusUpperTail.MarkedRealDiagonalGaussianEnergy
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The upper matrix's characteristic polynomial depends only on its
marked scalar and complementary block, in the explicit product coordinates. -/
theorem markedRealDiagonal_join_charpoly
    (m : ℕ) (hm : 0 < m)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ)
    (u : RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ) :
    (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u).charpoly =
      (Polynomial.X -
        Polynomial.C (markedRealDiagonalProductEquiv m d).1) *
        (Matrix.of (markedRealDiagonalProductEquiv m d).2.curry).charpoly := by
  let S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m) :=
    (realSchurMixedUpperEntryEquiv (markedRealTwoBlockSizes m)).symm (d,u)
  have h := markedRealTwoBlock_charpoly_factor m hm S.val 1
    S.property (by simp)
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h
  change (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u).charpoly =
    (Polynomial.X - Polynomial.C
      (markedRealScalar m
        (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u))) *
      (markedRealComplement m
        (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u)).charpoly at h
  rw [markedRealDiagonal_join_scalar, markedRealDiagonal_join_complement] at h
  exact h

#print axioms markedRealDiagonal_join_charpoly
end SpectralRadiusUpperTail
