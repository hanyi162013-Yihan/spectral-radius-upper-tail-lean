import SpectralRadiusUpperTail.MarkedRealDiagonalProductVolume
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The Gaussian quadratic energy splits exactly into the scalar and
complementary matrix entries. -/
theorem markedRealDiagonal_energy_split (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) :
    (∑ p : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m),
      (d p)^2) =
      (markedRealDiagonalProductEquiv m d).1 ^ 2 +
        ∑ ij : Fin m × Fin m,
          ((markedRealDiagonalProductEquiv m d).2 ij)^2 := by
  let e := markedRealDiagonalEntryEquiv m
  have hsum :
      (∑ q : Unit ⊕ (Fin m × Fin m), (d (e q))^2) =
        ∑ p : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m),
          (d p)^2 := by
    apply Fintype.sum_equiv e
    intro q
    rfl
  rw [← hsum]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  change (d (markedRealScalarDiagonalEntry m)) ^ 2 +
    (∑ ij : Fin m × Fin m,
      (d (markedRealComplementDiagonalEntry m ij.1 ij.2)) ^ 2) = _
  rw [markedRealDiagonalProductEquiv_fst]
  congr 1

/-- The scalar and complementary block of the upper matrix are exactly
the two components of the diagonal-coordinate product. -/
theorem markedRealDiagonal_join_scalar (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ)
    (u : RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ) :
    markedRealScalar m
      (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u) =
        (markedRealDiagonalProductEquiv m d).1 := by
  rw [markedRealDiagonalProductEquiv_fst]
  rfl

theorem markedRealDiagonal_join_complement (m : ℕ)
    (d : RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ)
    (u : RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ) :
    markedRealComplement m
      (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u) =
        Matrix.of (markedRealDiagonalProductEquiv m d).2.curry := by
  ext i j
  change (realSchurMixedUpperEntryJoin (markedRealTwoBlockSizes m) d u)
    ⟨1,i⟩ ⟨1,j⟩ = (markedRealDiagonalProductEquiv m d).2 (i,j)
  rw [markedRealDiagonalProductEquiv_snd]
  rfl

#print axioms markedRealDiagonal_energy_split
#print axioms markedRealDiagonal_join_scalar
#print axioms markedRealDiagonal_join_complement
end SpectralRadiusUpperTail
