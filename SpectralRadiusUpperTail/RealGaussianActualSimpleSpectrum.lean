import SpectralRadiusUpperTail.RealGaussianSimpleSpectrum
import SpectralRadiusUpperTail.GaussianMatrixAbsoluteContinuity

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The characteristic polynomial of an actual iid real Gaussian matrix
is separable almost surely, including in the zero-dimensional case.
This excludes repeated complex eigenvalues before any real Schur chart or
one-point intensity formula is used. -/
theorem realGaussianMatrix_charpoly_separable_ae (n : ℕ) :
    ∀ᵐ x ∂gaussianMatrixLaw n,
      (Matrix.of x.curry).charpoly.Separable := by
  exact (gaussianMatrixLaw_absolutelyContinuous_volume n).ae_le
    (charpoly_separable_ae_volume n)

#print axioms realGaussianMatrix_charpoly_separable_ae
end SpectralRadiusUpperTail
