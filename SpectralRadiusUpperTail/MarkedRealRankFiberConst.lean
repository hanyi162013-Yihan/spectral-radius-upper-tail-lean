import SpectralRadiusUpperTail.MarkedRealAngularRankSource
import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial
open scoped Matrix

/-- The characteristic polynomial of a two-block upper matrix is
unaffected by changing its free strictly-upper row. -/
theorem markedRealUpper_charpoly_eq_of_diagonal_blocks
    (m : ℕ) (hm : 0 < m)
    (S T : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m))
    (hdiag : ∀ i a b,
      S.val ⟨i,a⟩ ⟨i,b⟩ = T.val ⟨i,a⟩ ⟨i,b⟩) :
    S.val.charpoly = T.val.charpoly := by
  have hs : markedRealScalar m S.val = markedRealScalar m T.val :=
    hdiag 0 (markedRealZeroCoordinate m) (markedRealZeroCoordinate m)
  have hc : markedRealComplement m S.val = markedRealComplement m T.val := by
    ext i j
    exact hdiag 1 i j
  have hS := markedRealTwoBlock_charpoly_factor m hm S.val 1 S.property (by simp)
  have hT := markedRealTwoBlock_charpoly_factor m hm T.val 1 T.property (by simp)
  simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at hS hT
  rw [hS, hT, hs, hc]

/-- The real-root rank restriction remains constant on every free
upper-row Gaussian fiber. -/
theorem markedRealUpperRankSource_iff_of_diagonal_blocks
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (S T : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m))
    (hdiag : ∀ i a c,
      S.val ⟨i,a⟩ ⟨i,c⟩ = T.val ⟨i,a⟩ ⟨i,c⟩) :
    S ∈ markedRealUpperRankSource m k b ↔
      T ∈ markedRealUpperRankSource m k b := by
  have hp := markedRealUpper_charpoly_eq_of_diagonal_blocks m hm S T hdiag
  have hs : markedRealScalar m S.val = markedRealScalar m T.val :=
    hdiag 0 (markedRealZeroCoordinate m) (markedRealZeroCoordinate m)
  simp only [markedRealUpperRankSource, Set.mem_setOf_eq, hp, hs]

#print axioms markedRealUpperRankSource_iff_of_diagonal_blocks
end SpectralRadiusUpperTail
