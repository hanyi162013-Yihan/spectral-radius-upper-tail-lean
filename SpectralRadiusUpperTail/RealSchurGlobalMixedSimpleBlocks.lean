import SpectralRadiusUpperTail.RealSchurGlobalMixedBlockUpper
import SpectralRadiusUpperTail.RealSchurMixedSeparatedBlocks
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The shape produced by the real-Schur recursion has no empty blocks. -/
theorem realSchurListBlockSize_pos
    (s : List ℕ) (hs : ∀ k ∈ s, k = 1 ∨ k = 2)
    (i : Fin s.length) : 0 < realSchurListBlockSize s i := by
  induction s with
  | nil => exact i.elim0
  | cons k ks ih =>
      induction i using Fin.cases with
      | zero =>
          change 0 < k
          rcases hs k (by simp) with h | h <;> omega
      | succ i =>
          change 0 < realSchurListBlockSize ks i
          exact ih (by
            intro x hx
            exact hs x (by simp [hx])) i

/-- A simple-spectrum real endomorphism has a global mixed 1×1/2×2
block-upper representation whose different diagonal-block characteristic
polynomials are pairwise coprime. -/
theorem realLinearMap_exists_mixed_simple_blocks
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E)
    (hsep : f.charpoly.Separable) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ b : OrthonormalBasis
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ E,
        let T := LinearMap.toMatrix b.toBasis b.toBasis f
        realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 ∧
        Pairwise (fun i j : Fin s.length =>
          IsCoprime
            (T.toSquareBlock
              (fun z : RealSchurMixedCoord (realSchurListBlockSize s) => z.1) i).charpoly
            (T.toSquareBlock
              (fun z : RealSchurMixedCoord (realSchurListBlockSize s) => z.1) j).charpoly) := by
  obtain ⟨s, hs, b, hb⟩ := realLinearMap_exists_mixed_block_upper f
  refine ⟨s, hs, b, ?_⟩
  let T := LinearMap.toMatrix b.toBasis b.toBasis f
  have hT : realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 :=
    (realSchurMixed_blockTriangular_iff_lower_zero _ T).mp hb
  refine ⟨hT, ?_⟩
  have hchar : f.charpoly = T.charpoly :=
    (f.charpoly_toMatrix b.toBasis).symm
  have hTsep : T.charpoly.Separable := by
    rw [← hchar]
    exact hsep
  exact realSchurMixed_blockUpper_charpoly_pairwise_coprime
    (realSchurListBlockSize s)
    (realSchurListBlockSize_pos s hs) T hT hTsep

#print axioms realLinearMap_exists_mixed_simple_blocks
end SpectralRadiusUpperTail
