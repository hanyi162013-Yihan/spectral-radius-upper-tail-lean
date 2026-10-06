import SpectralRadiusUpperTail.RealSchurMixedUpperAlgebra
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Every named Schur block occurs among the global scalar-coordinate
indices when its size is positive. -/
theorem realSchurMixed_blockIndex_surjective
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) :
    Function.Surjective (fun z : RealSchurMixedCoord s => z.1) := by
  intro i
  exact ⟨⟨i,⟨0,hs i⟩⟩,rfl⟩

/-- The characteristic polynomial of a block-upper real matrix is the
product of the characteristic polynomials of its diagonal blocks. Here
`toSquareBlock` carries the native subtype index of each block. -/
theorem realSchurMixed_blockUpper_charpoly
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0) :
    T.charpoly =
      ∏ i : Fin m,
        (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) i).charpoly := by
  have hb : T.BlockTriangular (fun z : RealSchurMixedCoord s => z.1) :=
    (realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hT
  rw [hb.charpoly,
    Finset.image_univ_of_surjective (realSchurMixed_blockIndex_surjective s hs)]

#print axioms realSchurMixed_blockUpper_charpoly
end SpectralRadiusUpperTail
