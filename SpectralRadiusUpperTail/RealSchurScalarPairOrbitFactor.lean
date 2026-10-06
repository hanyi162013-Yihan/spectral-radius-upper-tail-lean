import SpectralRadiusUpperTail.RealSchurJacobianPairFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A scalar block followed by a conjugate-pair block in a 3×3 real Schur
matrix. -/
def realSchurScalarPairDiagonal (a x b c : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, 0, 0; 0, x, b; 0, -c, x]

/-- The two skew directions mixing the scalar coordinate with the pair. -/
def realSchurScalarPairGenerator (p q : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -p, -q; p, 0, 0; q, 0, 0]

/-- The lower-left block of the actual infinitesimal conjugation is the
scalar–pair Sylvester operator, up to an irrelevant sign. Thus its
determinant is the previously computed scalar–pair spectral-gap factor. -/
theorem realSchur_scalar_pair_orbit_sylvester
    (a x b c p q : ℝ) (i : Fin 2) :
    ![(realSchurScalarPairGenerator p q *
          realSchurScalarPairDiagonal a x b c -
        realSchurScalarPairDiagonal a x b c *
          realSchurScalarPairGenerator p q) 1 0,
      (realSchurScalarPairGenerator p q *
          realSchurScalarPairDiagonal a x b c -
        realSchurScalarPairDiagonal a x b c *
          realSchurScalarPairGenerator p q) 2 0] i =
      -((realSchurBlock x b c - Matrix.scalar (Fin 2) a).mulVec
        ![p,q]) i := by
  fin_cases i <;>
    simp [realSchurScalarPairGenerator, realSchurScalarPairDiagonal,
      realSchurBlock, Matrix.scalar, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_two] <;>
    ring

#print axioms realSchur_scalar_pair_orbit_sylvester
end SpectralRadiusUpperTail
