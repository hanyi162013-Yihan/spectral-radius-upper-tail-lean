import SpectralRadiusUpperTail.RealSchurAlmostEverywhereRegular
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- An actual iid real Gaussian matrix almost surely admits an
orthonormal regular mixed real-Schur block representation. -/
theorem realGaussianMatrix_exists_regular_mixed_block_upper_ae
    (n : ℕ) :
    ∀ᵐ A : (Fin n × Fin n) → ℝ ∂gaussianMatrixLaw n,
      ∃ s : List ℕ,
        (∀ k ∈ s, k = 1 ∨ k = 2) ∧
        ∃ b : OrthonormalBasis
          (RealSchurMixedCoord (realSchurListBlockSize s)) ℝ
          (EuclideanSpace ℝ (Fin n)),
          let T := LinearMap.toMatrix b.toBasis b.toBasis
            (Matrix.of A.curry).toEuclideanLin
          realSchurMixedLowerProjection (realSchurListBlockSize s) T = 0 ∧
          (realSchurMixedOrbitMatrix (realSchurListBlockSize s) T).det ≠ 0 := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with A hA
  exact realMatrix_exists_regular_mixed_block_upper_of_separable
    (Matrix.of A.curry) hA

#print axioms realGaussianMatrix_exists_regular_mixed_block_upper_ae
end SpectralRadiusUpperTail
