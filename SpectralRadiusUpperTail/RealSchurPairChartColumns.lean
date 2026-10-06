import SpectralRadiusUpperTail.RealSchurPairOrbitDerivative
import SpectralRadiusUpperTail.RealSchurJacobianPairPair
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The first column of the local 4×4 Jacobian is the exact displacement
when the common real part of a pair block changes. -/
theorem realSchur_pair_chart_x_column (t x b c : ℝ) :
    realSchurBridgeVector
      (realSchurBlock (x+t) b c - realSchurBlock x b c) =
      fun i => t * realSchurPairOrbitJacobian b c i 0 := by
  funext i
  fin_cases i <;>
    simp [realSchurBridgeVector, realSchurBlock,
      realSchurPairOrbitJacobian, Matrix.sub_apply] <;>
    ring

/-- The second column is the exact displacement in the upper off-diagonal
Schur parameter. -/
theorem realSchur_pair_chart_b_column (t x b c : ℝ) :
    realSchurBridgeVector
      (realSchurBlock x (b+t) c - realSchurBlock x b c) =
      fun i => t * realSchurPairOrbitJacobian b c i 1 := by
  funext i
  fin_cases i <;>
    simp [realSchurBridgeVector, realSchurBlock,
      realSchurPairOrbitJacobian, Matrix.sub_apply] <;>
    ring

/-- The third column is the exact displacement in the lower off-diagonal
Schur parameter. -/
theorem realSchur_pair_chart_c_column (t x b c : ℝ) :
    realSchurBridgeVector
      (realSchurBlock x b (c+t) - realSchurBlock x b c) =
      fun i => t * realSchurPairOrbitJacobian b c i 2 := by
  funext i
  fin_cases i <;>
    simp [realSchurBridgeVector, realSchurBlock,
      realSchurPairOrbitJacobian, Matrix.sub_apply] <;>
    ring

/-- The last candidate Jacobian column is the infinitesimal actual
rotation orbit. Together with the three exact affine columns, this checks
all coordinate directions at angle zero. A four-dimensional measure
change remains separate. -/
theorem realSchur_pair_chart_angle_column (x b c : ℝ) (i j : Fin 2) :
    HasDerivAt (fun θ : ℝ =>
      (realSchurRotation θ * realSchurBlock x b c *
        (realSchurRotation θ)ᵀ) i j)
      (realSchurPairOrbitJacobian b c
        (if i = 0 then (if j = 0 then 0 else 1)
          else (if j = 0 then 2 else 3)) 3) 0 := by
  convert realSchur_rotation_orbit_hasDerivAt_zero x b c i j using 1
  rw [realSchur_pair_orbit_commutator]
  fin_cases i <;> fin_cases j <;>
    simp [realSchurPairOrbitJacobian]

#print axioms realSchur_pair_chart_x_column
#print axioms realSchur_pair_chart_b_column
#print axioms realSchur_pair_chart_c_column
#print axioms realSchur_pair_chart_angle_column
end SpectralRadiusUpperTail
