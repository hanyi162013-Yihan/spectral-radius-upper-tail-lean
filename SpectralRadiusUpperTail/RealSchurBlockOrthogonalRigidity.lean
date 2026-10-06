import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- An orthogonal matrix that preserves an ordered block flag cannot
mix distinct blocks: its inverse is both block upper and its transpose. -/
theorem orthogonal_blockTriangular_offBlock
    {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]
    (b : ι → β) (Q : Matrix ι ι ℝ)
    (hQ : Q.transpose * Q = 1) (hUpper : Q.BlockTriangular b)
    (i j : ι) (hij : b i ≠ b j) : Q i j = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · letI : Invertible Q := invertibleOfLeftInverse Q Q.transpose hQ
    have hInv : (Q⁻¹).BlockTriangular b :=
      Matrix.blockTriangular_inv_of_blockTriangular hUpper
    have hzero : Q⁻¹ j i = 0 := hInv h
    rw [Matrix.inv_eq_left_inv hQ, Matrix.transpose_apply] at hzero
    exact hzero
  · exact hUpper h

#print axioms orthogonal_blockTriangular_offBlock
end SpectralRadiusUpperTail
