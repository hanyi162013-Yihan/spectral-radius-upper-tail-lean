import SpectralRadiusUpperTail.RealSchurOrthogonalCompression
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
universe u

/-- A nested sum of finite block-coordinate sets. -/
def RealSchurRecursiveBlockIndex : List ℕ → Type
  | [] => Empty
  | k :: ks => Fin k ⊕ RealSchurRecursiveBlockIndex ks

instance (s : List ℕ) : Fintype (RealSchurRecursiveBlockIndex s) := by
  induction s with
  | nil =>
      change Fintype Empty
      infer_instance
  | cons k ks ih =>
      letI := ih
      change Fintype (Fin k ⊕ RealSchurRecursiveBlockIndex ks)
      infer_instance

instance (s : List ℕ) : DecidableEq (RealSchurRecursiveBlockIndex s) := by
  induction s with
  | nil =>
      change DecidableEq Empty
      infer_instance
  | cons k ks ih =>
      letI := ih
      change DecidableEq (Fin k ⊕ RealSchurRecursiveBlockIndex ks)
      infer_instance

/-- Recursive block-upper-triangularity, with block sizes listed in `s`. -/
def RealSchurRecursiveBlockUpper :
    (s : List ℕ) →
    Matrix (RealSchurRecursiveBlockIndex s)
      (RealSchurRecursiveBlockIndex s) ℝ → Prop
  | [], _ => True
  | k :: ks, A =>
      (∀ i : RealSchurRecursiveBlockIndex ks, ∀ j : Fin k,
        A (Sum.inr i) (Sum.inl j) = 0) ∧
      RealSchurRecursiveBlockUpper ks (A.submatrix Sum.inr Sum.inr)

private theorem realLinearMap_exists_recursive_block_upper_of_finrank
    (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E),
      Module.finrank ℝ E = n →
        ∃ s : List ℕ,
          (∀ k ∈ s, k = 1 ∨ k = 2) ∧
          ∃ b : OrthonormalBasis (RealSchurRecursiveBlockIndex s) ℝ E,
            RealSchurRecursiveBlockUpper s
              (LinearMap.toMatrix b.toBasis b.toBasis f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro E _ _ _ f hdim
      by_cases hzero : n = 0
      · have he : Fintype.card (Fin (Module.finrank ℝ E)) =
            Fintype.card (RealSchurRecursiveBlockIndex []) := by
          simp [RealSchurRecursiveBlockIndex, hdim, hzero, Fintype.card_empty]
        let b : OrthonormalBasis (RealSchurRecursiveBlockIndex []) ℝ E :=
          (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq he)
        exact ⟨[], by simp, b, trivial⟩
      · have hpos : 0 < Module.finrank ℝ E := by omega
        obtain ⟨P,hRank,hInv⟩ :=
          realLinearMap_exists_invariant_subspace_rank_one_or_two hpos f
        have hless : Module.finrank ℝ Pᗮ < n := by
          have hsum := P.finrank_add_finrank_orthogonal
          rcases hRank with h1 | h2 <;> omega
        let g := realSchurOrthogonalCompression f P
        obtain ⟨ks,hks,v,hv⟩ := ih _ hless (Pᗮ) g rfl
        let a := stdOrthonormalBasis ℝ P
        let b := realSchurOrthogonalJoinBasis P a v
        refine ⟨Module.finrank ℝ P :: ks, ?_, b, ?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hRank
          · exact hks k hk
        · change (∀ i : RealSchurRecursiveBlockIndex ks,
              ∀ j : Fin (Module.finrank ℝ P),
              (LinearMap.toMatrix b.toBasis b.toBasis f)
                (Sum.inr i) (Sum.inl j) = 0) ∧
            RealSchurRecursiveBlockUpper ks
              ((LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inr Sum.inr)
          constructor
          · intro i j
            exact realSchurOrthogonalJoinBasis_lowerLeft_zero f P hInv a v i j
          · have hmat :
                (LinearMap.toMatrix b.toBasis b.toBasis f).submatrix Sum.inr Sum.inr =
                  LinearMap.toMatrix v.toBasis v.toBasis g := by
                ext i j
                exact realSchurOrthogonalJoinBasis_lowerRight_eq f P a v i j
            rw [hmat]
            exact hv

/-- Every finite-dimensional real endomorphism has an orthonormal
block-upper-triangular representation with blocks of size one or two.
This gives global deterministic block coverage; it does not yet
identify canonical pair coordinates or a Gaussian Jacobian. -/
theorem realLinearMap_exists_recursive_block_upper
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] E) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ b : OrthonormalBasis (RealSchurRecursiveBlockIndex s) ℝ E,
        RealSchurRecursiveBlockUpper s
          (LinearMap.toMatrix b.toBasis b.toBasis f) :=
  realLinearMap_exists_recursive_block_upper_of_finrank
    (Module.finrank ℝ E) E f rfl

#print axioms realLinearMap_exists_recursive_block_upper
end SpectralRadiusUpperTail
