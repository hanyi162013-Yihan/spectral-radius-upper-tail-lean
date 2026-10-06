import SpectralRadiusUpperTail.RealSchurAlmostEverywhereRegular
import SpectralRadiusUpperTail.RealSchurOrthonormalConjugation
import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A regular adapted Schur frame of a fixed matrix becomes an actual
orthogonal-conjugation frame after reindexing its original coordinates
by the finite equivalence between the two orthonormal bases. -/
theorem realMatrix_exists_reindexed_regular_frame_of_separable
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsep : A.charpoly.Separable) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
      ∃ c : RealSchurMixedRegularFrame (realSchurListBlockSize s),
        Matrix.reindex e e A = c.Q * c.T * c.Qᵀ := by
  obtain ⟨s, hs, b, hT, hdet⟩ :=
    realMatrix_exists_regular_mixed_block_upper_of_separable A hsep
  let u : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s) :=
    u.toBasis.indexEquiv b.toBasis
  let u' := u.reindex e
  let Q := u'.toBasis.toMatrix b
  let T := LinearMap.toMatrix b.toBasis b.toBasis A.toEuclideanLin
  obtain ⟨hQ, hconj⟩ :=
    realOrthonormalBasis_matrix_conjugation u' b A.toEuclideanLin
  have hstd : LinearMap.toMatrix u.toBasis u.toBasis A.toEuclideanLin = A := by
    change LinearMap.toMatrix u.toBasis u.toBasis
      (Matrix.toLin u.toBasis u.toBasis A) = A
    exact LinearMap.toMatrix_toLin u.toBasis u.toBasis A
  have hreidx : LinearMap.toMatrix u'.toBasis u'.toBasis A.toEuclideanLin =
      Matrix.reindex e e A := by
    calc
      _ = Matrix.reindex e e
          (LinearMap.toMatrix u.toBasis u.toBasis A.toEuclideanLin) :=
        LinearMap.toMatrixOrthonormal_reindex u e A.toEuclideanLin
      _ = Matrix.reindex e e A := by rw [hstd]
  let c : RealSchurMixedRegularFrame (realSchurListBlockSize s) :=
    ⟨T, hT, hdet, Q, hQ⟩
  refine ⟨s, hs, e, c, ?_⟩
  change Matrix.reindex e e A = Q * T * Qᵀ
  rw [← hreidx]
  exact hconj

#print axioms realMatrix_exists_reindexed_regular_frame_of_separable
end SpectralRadiusUpperTail
