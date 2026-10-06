import SpectralRadiusUpperTail.RealSchurAtomicInvariantSeed
import SpectralRadiusUpperTail.RealSchurOrthogonalRestrictionBlock
import SpectralRadiusUpperTail.RealSchurRecursiveBlockUpper

namespace SpectralRadiusUpperTail
universe u

/-- Each two-dimensional diagonal block has no real characteristic root. -/
def RealSchurRecursiveAtomicBlocks : (s : List ℕ) →
    Matrix (RealSchurRecursiveBlockIndex s) (RealSchurRecursiveBlockIndex s) ℝ → Prop
  | [], _ => True
  | k :: ks, A =>
      (k=2 → ∀ a : ℝ, (A.submatrix Sum.inl Sum.inl).charpoly.eval a ≠ 0) ∧
      RealSchurRecursiveAtomicBlocks ks (A.submatrix Sum.inr Sum.inr)

private theorem realLinearMap_exists_recursive_atomic_blocks_of_finrank
    (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E), Module.finrank ℝ E=n →
      ∃ s : List ℕ, (∀ k ∈ s, k=1 ∨ k=2) ∧
        ∃ b : OrthonormalBasis (RealSchurRecursiveBlockIndex s) ℝ E,
          RealSchurRecursiveBlockUpper s (LinearMap.toMatrix b.toBasis b.toBasis f) ∧
          RealSchurRecursiveAtomicBlocks s (LinearMap.toMatrix b.toBasis b.toBasis f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro E _ _ _ f hdim
      by_cases hzero : n=0
      · have he : Fintype.card (Fin (Module.finrank ℝ E))=
            Fintype.card (RealSchurRecursiveBlockIndex []) := by
          simp [RealSchurRecursiveBlockIndex,hdim,hzero,Fintype.card_empty]
        let b : OrthonormalBasis (RealSchurRecursiveBlockIndex []) ℝ E :=
          (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq he)
        exact ⟨[],by simp,b,trivial,trivial⟩
      · have hpos : 0 < Module.finrank ℝ E := by omega
        obtain ⟨P,hRank,hInv,hAtomic⟩ := realLinearMap_exists_atomic_invariant_seed hpos f
        have hless : Module.finrank ℝ Pᗮ < n := by
          have hsum := P.finrank_add_finrank_orthogonal
          rcases hRank with h1 | h2 <;> omega
        let g := realSchurOrthogonalCompression f P
        obtain ⟨ks,hks,v,hv,hva⟩ := ih _ hless (Pᗮ) g rfl
        let a := stdOrthonormalBasis ℝ P
        let b := realSchurOrthogonalJoinBasis P a v
        have hmat : (LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inr Sum.inr =
            LinearMap.toMatrix v.toBasis v.toBasis g := by
          ext i j
          exact realSchurOrthogonalJoinBasis_lowerRight_eq f P a v i j
        have htop : (LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inl Sum.inl =
            LinearMap.toMatrix a.toBasis a.toBasis (f.restrict hInv) := by
          ext i j
          exact realSchurOrthogonalJoinBasis_upperLeft_eq f P hInv a v i j
        refine ⟨Module.finrank ℝ P :: ks,?_,b,?_,?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hRank
          · exact hks k hk
        · constructor
          · intro i j
            exact realSchurOrthogonalJoinBasis_lowerLeft_zero f P hInv a v i j
          · change RealSchurRecursiveBlockUpper ks
              ((LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inr Sum.inr)
            rw [hmat]
            exact hv
        · constructor
          · intro htwo x
            change ((LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inl Sum.inl).charpoly.eval x ≠ 0
            rw [htop,(f.restrict hInv).charpoly_toMatrix a.toBasis]
            exact hAtomic htwo x
          · change RealSchurRecursiveAtomicBlocks ks
              ((LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inr Sum.inr)
            rw [hmat]
            exact hva

/-- Global real Schur coverage by scalar real blocks and indivisible
nonreal conjugate-pair blocks, in recursively joined orthonormal coordinates. -/
theorem realLinearMap_exists_recursive_atomic_blocks
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    ∃ s : List ℕ, (∀ k ∈ s, k=1 ∨ k=2) ∧
      ∃ b : OrthonormalBasis (RealSchurRecursiveBlockIndex s) ℝ E,
        RealSchurRecursiveBlockUpper s (LinearMap.toMatrix b.toBasis b.toBasis f) ∧
        RealSchurRecursiveAtomicBlocks s (LinearMap.toMatrix b.toBasis b.toBasis f) :=
  realLinearMap_exists_recursive_atomic_blocks_of_finrank (Module.finrank ℝ E) E f rfl

#print axioms realLinearMap_exists_recursive_atomic_blocks
end SpectralRadiusUpperTail
