import SpectralRadiusUpperTail.RealSchurJacobianPairFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The four-dimensional real Sylvester operator between two conjugate-pair
Schur blocks, in the coordinate order `(p,q,r,s)` for a 2 by 2 bridge. -/
def realSchurPairPairSylvester (x b c u d e : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![x-u, e, b, 0;
      -d, x-u, 0, b;
      -c, 0, x-u, e;
      0, -c, -d, x-u]

def realSchurBridgeVector (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Fin 4 → ℝ := ![X 0 0, X 0 1, X 1 0, X 1 1]

theorem realSchur_pair_pair_sylvester_action
    (x b c u d e : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    realSchurBridgeVector
      (realSchurBlock x b c * X - X * realSchurBlock u d e) =
      (realSchurPairPairSylvester x b c u d e).mulVec
        (realSchurBridgeVector X) := by
  funext i
  fin_cases i <;>
    simp [realSchurBridgeVector, realSchurPairPairSylvester,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
      Matrix.sub_apply, realSchurBlock, Fin.sum_univ_succ,
      Fin.sum_univ_two] <;>
    ring

theorem realSchur_pair_pair_factor (x b c u d e y v : ℝ)
    (hbc : b*c = y^2) (hde : d*e = v^2) :
    Matrix.det (realSchurPairPairSylvester x b c u d e) =
      (((x-u)^2+(y-v)^2)*((x-u)^2+(y+v)^2)) := by
  have hdet : Matrix.det (realSchurPairPairSylvester x b c u d e) =
      ((x-u)^2+b*c+d*e)^2-4*(b*c)*(d*e) := by
    simp [realSchurPairPairSylvester, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ]
    have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
    have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
    simp [h12, h22] at *
    ring
  rw [hdet, hbc, hde]
  ring

#print axioms realSchur_pair_pair_factor
#print axioms realSchur_pair_pair_sylvester_action
end SpectralRadiusUpperTail
