import SpectralRadiusUpperTail.RealSchurRecursiveBlockOrder
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A recursively upper-block-triangular matrix remains upper-block-triangular
in the dependent-sum coordinate system used by the mixed real-Schur charts. -/
theorem realSchurRecursiveBlockUpper_reindex_mixed
    (s : List ℕ)
    (A : Matrix (RealSchurRecursiveBlockIndex s)
      (RealSchurRecursiveBlockIndex s) ℝ)
    (hA : RealSchurRecursiveBlockUpper s A)
    (i j : RealSchurMixedCoord (realSchurListBlockSize s))
    (hij : j.1 < i.1) :
    Matrix.reindex (realSchurRecursiveMixedIndexEquiv s)
      (realSchurRecursiveMixedIndexEquiv s) A i j = 0 := by
  let e := realSchurRecursiveMixedIndexEquiv s
  rw [Matrix.reindex_apply]
  apply realSchurRecursiveBlockUpper_lower_zero s A hA
  have hi : i.1.val = realSchurRecursiveBlockNumber s (e.symm i) := by
    simpa [e] using realSchurRecursiveMixedIndexEquiv_blockNumber s (e.symm i)
  have hj : j.1.val = realSchurRecursiveBlockNumber s (e.symm j) := by
    simpa [e] using realSchurRecursiveMixedIndexEquiv_blockNumber s (e.symm j)
  rw [← hi, ← hj]
  exact hij

/-- Every finite-dimensional real endomorphism has a mixed-coordinate
orthonormal basis with 1×1 and 2×2 diagonal blocks and all entries below
the block diagonal equal to zero. No spectral separation or canonical pair
orientation is asserted here. -/
theorem realLinearMap_exists_mixed_block_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ b : OrthonormalBasis
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ E,
        ∀ i j : RealSchurMixedCoord (realSchurListBlockSize s),
          j.1 < i.1 →
            (LinearMap.toMatrix b.toBasis b.toBasis f) i j = 0 := by
  obtain ⟨s, hs, b, hb⟩ := realLinearMap_exists_recursive_block_upper f
  let e := realSchurRecursiveMixedIndexEquiv s
  let b' := b.reindex e
  refine ⟨s, hs, b', ?_⟩
  intro i j hij
  have hmat : LinearMap.toMatrix b'.toBasis b'.toBasis f =
      Matrix.reindex e e (LinearMap.toMatrix b.toBasis b.toBasis f) := by
    exact LinearMap.toMatrixOrthonormal_reindex b e f
  rw [hmat]
  exact realSchurRecursiveBlockUpper_reindex_mixed s
    (LinearMap.toMatrix b.toBasis b.toBasis f) hb i j hij

#print axioms realLinearMap_exists_mixed_block_upper
end SpectralRadiusUpperTail
