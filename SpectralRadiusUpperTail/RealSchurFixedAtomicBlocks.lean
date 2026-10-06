import SpectralRadiusUpperTail.RealSchurMixedAtomicCoverage
import SpectralRadiusUpperTail.RealSchurFixedMatrixRegularFrame
import SpectralRadiusUpperTail.RealSchurMixedFlagAtlas

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Every real matrix has an orthogonal mixed Schur representation
with only real scalar blocks and nonreal conjugate-pair blocks. -/
theorem realMatrix_exists_reindexed_atomic_blocks
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ s : List ℕ, (∀ k ∈ s, k=1 ∨ k=2) ∧
      ∃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
      ∃ Q : RealSchurMixedOrthogonalFrame (realSchurListBlockSize s),
      ∃ T : Matrix (RealSchurMixedCoord (realSchurListBlockSize s))
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ,
        realSchurMixedLowerProjection (realSchurListBlockSize s) T=0 ∧
        (∀ i, realSchurListBlockSize s i=2 → ∀ a : ℝ,
          (realSchurMixedDiagonalMatrix (realSchurListBlockSize s) T i).charpoly.eval a ≠ 0) ∧
        Matrix.reindex e e A=Q.val*T*Q.valᵀ := by
  obtain ⟨s,hs,b,hT,hAtomic⟩ := realLinearMap_exists_mixed_atomic_blocks A.toEuclideanLin
  let u : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  let e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s) :=
    u.toBasis.indexEquiv b.toBasis
  let u' := u.reindex e
  let Q := u'.toBasis.toMatrix b
  let T := LinearMap.toMatrix b.toBasis b.toBasis A.toEuclideanLin
  obtain ⟨hQ,hconj⟩ := realOrthonormalBasis_matrix_conjugation u' b A.toEuclideanLin
  have hstd : LinearMap.toMatrix u.toBasis u.toBasis A.toEuclideanLin=A := by
    change LinearMap.toMatrix u.toBasis u.toBasis (Matrix.toLin u.toBasis u.toBasis A)=A
    exact LinearMap.toMatrix_toLin u.toBasis u.toBasis A
  have hreidx : LinearMap.toMatrix u'.toBasis u'.toBasis A.toEuclideanLin=Matrix.reindex e e A := by
    calc
      _ = Matrix.reindex e e (LinearMap.toMatrix u.toBasis u.toBasis A.toEuclideanLin) :=
        LinearMap.toMatrixOrthonormal_reindex u e A.toEuclideanLin
      _ = Matrix.reindex e e A := by rw [hstd]
  refine ⟨s,hs,e,⟨Q,hQ⟩,T,hT,hAtomic,?_⟩
  change Matrix.reindex e e A=Q*T*Qᵀ
  rw [← hreidx]
  exact hconj

#print axioms realMatrix_exists_reindexed_atomic_blocks
end SpectralRadiusUpperTail
