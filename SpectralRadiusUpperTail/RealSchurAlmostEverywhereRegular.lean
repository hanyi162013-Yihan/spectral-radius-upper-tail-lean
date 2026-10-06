import SpectralRadiusUpperTail.RealSchurGlobalRegularCoverage
import SpectralRadiusUpperTail.RealSchurMixedSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A fixed real matrix with simple characteristic spectrum has a regular
mixed-Schur block representation on its associated Euclidean space. -/
theorem realMatrix_exists_regular_mixed_block_upper_of_separable
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsep : A.charpoly.Separable) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ b : OrthonormalBasis
        (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ
        (EuclideanSpace ℝ (Fin n)),
        let T := LinearMap.toMatrix b.toBasis b.toBasis A.toEuclideanLin
        realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 ∧
        (realSchurMixedOrbitMatrix (realSchurListBlockSize s) T).det ≠ 0 := by
  have hchar : A.toEuclideanLin.charpoly = A.charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.charpoly_toLin A (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  apply realLinearMap_exists_regular_mixed_block_upper A.toEuclideanLin
  rw [hchar]
  exact hsep

/-- Almost every real matrix, in entrywise Lebesgue measure, has an
orthonormal regular 1×1/2×2 mixed-Schur representation. The statement
uses the original fixed matrix entries, with the frame allowed to vary. -/
theorem realMatrix_exists_regular_mixed_block_upper_ae_volume
    (n : ℕ) :
    ∀ᵐ A : (Fin n × Fin n) → ℝ,
      ∃ s : List ℕ,
        (∀ k ∈ s, k = 1 ∨ k = 2) ∧
        ∃ b : OrthonormalBasis
          (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ
          (EuclideanSpace ℝ (Fin n)),
          let T := LinearMap.toMatrix b.toBasis b.toBasis
            (Matrix.of A.curry).toEuclideanLin
          realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 ∧
          (realSchurMixedOrbitMatrix (realSchurListBlockSize s) T).det ≠ 0 := by
  filter_upwards [finiteRealMatrix_charpoly_separable_ae_volume (Fin n)]
    with A hA
  exact realMatrix_exists_regular_mixed_block_upper_of_separable
    (Matrix.of A.curry) hA

#print axioms realMatrix_exists_regular_mixed_block_upper_ae_volume
end SpectralRadiusUpperTail
