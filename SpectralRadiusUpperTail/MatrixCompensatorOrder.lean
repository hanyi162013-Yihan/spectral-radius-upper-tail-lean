import SpectralRadiusUpperTail.MatrixExponentialQuadratic
import Mathlib.Tactic.Module

namespace SpectralRadiusUpperTail
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- The remaining predictable correction is nonpositive. This uses
the actual positive-contraction square inequality, not entrywise order. -/
theorem matrix_compensator_correction_le_one {D : Matrix ι ι 𝕂}
    (hD : D.PosSemidef) (hn : ‖D‖ ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    1-s^2 • D+(4*s^4) • D^2 ≤ 1 := by
  have hsq : s^2 ≤ 1/4 := by nlinarith
  have hc : 0 ≤ s^2-4*s^4 := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hsq)]
  have hp : (D-D^2).PosSemidef :=
    Matrix.le_iff.mp (matrix_positive_contraction_square hD hn)
  have hq := (hp.smul (sq_nonneg s)).add ((hD.pow 2).smul hc)
  apply Matrix.le_iff.mpr
  convert hq using 1 <;> module

#print axioms matrix_compensator_correction_le_one
end SpectralRadiusUpperTail
