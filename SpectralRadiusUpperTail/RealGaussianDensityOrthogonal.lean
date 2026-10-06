import SpectralRadiusUpperTail.RealGaussianMatrixExplicitDensity
import SpectralRadiusUpperTail.MatrixUnitaryFrobenius
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

/-- The explicit real Gaussian entry density is unchanged by orthogonal
conjugation. This algebraic invariance is a prerequisite for real Schur
coordinates, independent of the Jacobian calculation. -/
theorem realGaussianMatrixWeight_orthogonal_conjugate
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    realGaussianMatrixWeight n
      (fun ij => ((U : Matrix (Fin n) (Fin n) ℝ) * A *
        (U : Matrix (Fin n) (Fin n) ℝ)ᴴ) ij.1 ij.2) =
      realGaussianMatrixWeight n (fun ij => A ij.1 ij.2) := by
  have hnorm := matrix_unitary_conjugation_frobenius_sq A U
  rw [real_frobenius_norm_sq, real_frobenius_norm_sq] at hnorm
  have hsum :
      (∑ ij : Fin n × Fin n,
        (((U : Matrix (Fin n) (Fin n) ℝ) * A *
          (U : Matrix (Fin n) (Fin n) ℝ)ᴴ) ij.1 ij.2)^2) =
      (∑ ij : Fin n × Fin n, (A ij.1 ij.2)^2) := by
    simpa only [Fintype.sum_prod_type] using hnorm
  unfold realGaussianMatrixWeight
  rw [hsum]

#print axioms realGaussianMatrixWeight_orthogonal_conjugate
end SpectralRadiusUpperTail
