import SpectralRadiusUpperTail.MatrixCoordinateMap
import SpectralRadiusUpperTail.HermitianDilation
import Mathlib.Data.Matrix.Basis

namespace SpectralRadiusUpperTail
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

lemma matrixCoordinateL_eq_single (i j : Fin N) (z : 𝕂) :
    matrixCoordinateL i j z = Matrix.single i j z := by
  ext p q
  simp [matrixCoordinateL_apply, Matrix.single, eq_comm]

lemma matrixCoordinate_mul_conjTranspose (i j : Fin N) (z : 𝕂) :
    matrixCoordinateL i j z * (matrixCoordinateL i j z).conjTranspose =
      Matrix.single i i ((‖z‖^2 : ℝ) : 𝕂) := by
  rw [matrixCoordinateL_eq_single]
  simp [RCLike.star_def, RCLike.mul_conj]

lemma matrixCoordinate_conjTranspose_mul (i j : Fin N) (z : 𝕂) :
    (matrixCoordinateL i j z).conjTranspose * matrixCoordinateL i j z =
      Matrix.single j j ((‖z‖^2 : ℝ) : 𝕂) := by
  rw [matrixCoordinateL_eq_single]
  simp [RCLike.star_def, RCLike.conj_mul]

/-- The actual dilation square has precisely one row-diagonal and one
column-diagonal entry, both equal to the scalar squared norm. -/
lemma matrixCoordinate_dilation_square (i j : Fin N) (z : 𝕂) :
    hermitianDilation (matrixCoordinateL i j z) * hermitianDilation (matrixCoordinateL i j z) =
      Matrix.fromBlocks (Matrix.single i i ((‖z‖^2 : ℝ) : 𝕂)) 0 0
        (Matrix.single j j ((‖z‖^2 : ℝ) : 𝕂)) := by
  rw [hermitianDilation_square, matrixCoordinate_mul_conjTranspose, matrixCoordinate_conjTranspose_mul]

#print axioms matrixCoordinate_dilation_square
end SpectralRadiusUpperTail
