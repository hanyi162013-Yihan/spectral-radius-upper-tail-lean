import SpectralRadiusUpperTail.RealSchurPairCoordinates
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Generator of counterclockwise rotations of the real plane. -/
def realSchurRotationGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0,-1;1,0]

/-- Infinitesimal orthogonal-conjugation direction at a real Schur pair
block. Its diagonal difference supplies the extra gap factor. -/
theorem realSchur_pair_orbit_commutator (x b c : ℝ) :
    realSchurRotationGenerator * realSchurBlock x b c -
      realSchurBlock x b c * realSchurRotationGenerator =
        !![c-b,0;0,b-c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotationGenerator, realSchurBlock,
      Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two] <;>
    ring

/-- Exact quadratic remainder for the infinitesimal rotation path. The
linear coefficient is the orbit commutator used in the local Jacobian. -/
theorem realSchur_pair_orbit_first_order (t x b c : ℝ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) +
        t • realSchurRotationGenerator) *
      realSchurBlock x b c *
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) -
        t • realSchurRotationGenerator) =
      realSchurBlock x b c +
        t • (realSchurRotationGenerator * realSchurBlock x b c -
          realSchurBlock x b c * realSchurRotationGenerator) -
        t^2 • (realSchurRotationGenerator * realSchurBlock x b c *
          realSchurRotationGenerator) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSchurRotationGenerator, realSchurBlock,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Fin.sum_univ_two] <;>
    ring

/-- Columns are the derivatives in `(x,b,c,angle)`; rows are the four
matrix-entry coordinates `(00,01,10,11)`. -/
def realSchurPairOrbitJacobian (b c : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,c-b;
      0,1,0,0;
      0,0,-1,0;
      1,0,0,b-c]

theorem realSchur_pair_orbit_jacobian_det (b c : ℝ) :
    Matrix.det (realSchurPairOrbitJacobian b c) = -2*(b-c) := by
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  simp [realSchurPairOrbitJacobian, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, h32]
  ring

theorem realSchur_pair_orbit_jacobian_abs (b c : ℝ)
    (hcb : c < b) :
    |Matrix.det (realSchurPairOrbitJacobian b c)| = 2*(b-c) := by
  rw [realSchur_pair_orbit_jacobian_det]
  rw [abs_of_nonpos (by linarith [sub_pos.mpr hcb] : -2*(b-c) ≤ 0)]
  ring

#print axioms realSchur_pair_orbit_commutator
#print axioms realSchur_pair_orbit_first_order
#print axioms realSchur_pair_orbit_jacobian_det
#print axioms realSchur_pair_orbit_jacobian_abs
end SpectralRadiusUpperTail
