import SpectralRadiusUpperTail.RealSchurMixedChartCharpoly
import SpectralRadiusUpperTail.RealSchurMixedSeparatedBlocks
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The diagonal block of a mixed-coordinate matrix, with its native
`Fin (s i)` index rather than the `toSquareBlock` subtype index. -/
def realSchurMixedDiagonalMatrix
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (i : Fin m) : Matrix (Fin (s i)) (Fin (s i)) ℝ :=
  fun a b => T ⟨i,a⟩ ⟨i,b⟩

theorem realSchurMixedDiagonalMatrix_charpoly
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (i : Fin m) :
    (T.toSquareBlock
      (fun z : RealSchurMixedCoord s => z.1) i).charpoly =
        (realSchurMixedDiagonalMatrix s T i).charpoly := by
  let e := realSchurMixedBlockFiberEquiv s i
  have heq : Matrix.reindex e.symm e.symm
      (T.toSquareBlock
        (fun z : RealSchurMixedCoord s => z.1) i) =
        realSchurMixedDiagonalMatrix s T i := by
    ext a b
    rfl
  calc
    _ = (Matrix.reindex e.symm e.symm
        (T.toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i)).charpoly :=
      (Matrix.charpoly_reindex e.symm _).symm
    _ = _ := by rw [heq]

theorem realSchurMixedSylvester_eq_diagonalMatrix
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (p : RealSchurLowerIndex m) :
    realSchurMixedSylvester s T p =
      realSchurRectangularSylvester
        (realSchurMixedDiagonalMatrix s T p.1.1)
        (realSchurMixedDiagonalMatrix s T p.1.2) := by
  exact realSchurMixedSylvester_eq_rectangular s T
    (realSchurMixedDiagonalMatrix s T) (by intro i a b; rfl) p

#print axioms realSchurMixedDiagonalMatrix_charpoly
end SpectralRadiusUpperTail
