import SpectralRadiusUpperTail.RealSchurRecursiveAtomicBlocks
import SpectralRadiusUpperTail.RealSchurGlobalMixedBlockUpper
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal

namespace SpectralRadiusUpperTail

/-- Indivisible two-dimensional blocks are preserved by the explicit
recursive-to-mixed coordinate equivalence. -/
theorem realSchurRecursiveAtomicBlocks_reindex_mixed
    (s : List ℕ) (A : Matrix (RealSchurRecursiveBlockIndex s)
      (RealSchurRecursiveBlockIndex s) ℝ)
    (hA : RealSchurRecursiveAtomicBlocks s A)
    (i : Fin s.length) (hi : realSchurListBlockSize s i=2) (a : ℝ) :
    (realSchurMixedDiagonalMatrix (realSchurListBlockSize s)
      (Matrix.reindex (realSchurRecursiveMixedIndexEquiv s)
        (realSchurRecursiveMixedIndexEquiv s) A) i).charpoly.eval a ≠ 0 := by
  induction s with
  | nil => exact i.elim0
  | cons k ks ih =>
      induction i using Fin.cases with
      | zero =>
          change k=2 at hi
          exact hA.1 hi a
      | succ i =>
          exact ih (A.submatrix Sum.inr Sum.inr) hA.2 i hi

/-- Every real endomorphism has a mixed orthonormal Schur representation
whose two-dimensional blocks have no real characteristic root. -/
theorem realLinearMap_exists_mixed_atomic_blocks
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    ∃ s : List ℕ, (∀ k ∈ s, k=1 ∨ k=2) ∧
      ∃ b : OrthonormalBasis (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ E,
        let T := LinearMap.toMatrix b.toBasis b.toBasis f
        realSchurMixedLowerProjection (realSchurListBlockSize s) T=0 ∧
        ∀ i, realSchurListBlockSize s i=2 → ∀ a : ℝ,
          (realSchurMixedDiagonalMatrix (realSchurListBlockSize s) T i).charpoly.eval a ≠ 0 := by
  obtain ⟨s,hs,b,hb,ha⟩ := realLinearMap_exists_recursive_atomic_blocks f
  let e := realSchurRecursiveMixedIndexEquiv s
  let b' := b.reindex e
  have hmat : LinearMap.toMatrix b'.toBasis b'.toBasis f =
      Matrix.reindex e e (LinearMap.toMatrix b.toBasis b.toBasis f) :=
    LinearMap.toMatrixOrthonormal_reindex b e f
  refine ⟨s,hs,b',?_,?_⟩
  · apply (realSchurMixed_blockTriangular_iff_lower_zero _ _).mp
    intro i j hij
    rw [hmat]
    exact realSchurRecursiveBlockUpper_reindex_mixed s
      (LinearMap.toMatrix b.toBasis b.toBasis f) hb i j hij
  · intro i hi a
    rw [hmat]
    exact realSchurRecursiveAtomicBlocks_reindex_mixed s
      (LinearMap.toMatrix b.toBasis b.toBasis f) ha i hi a

#print axioms realSchurRecursiveAtomicBlocks_reindex_mixed
#print axioms realLinearMap_exists_mixed_atomic_blocks
end SpectralRadiusUpperTail
