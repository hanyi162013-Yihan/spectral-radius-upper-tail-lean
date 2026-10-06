import SpectralRadiusUpperTail.RealSchurJacobianPairPair
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Two conjugate-pair blocks in a 4×4 real Schur matrix. -/
def realSchurPairPairDiagonal (x b c u d e : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![x, b, 0, 0;
      -c, x, 0, 0;
      0, 0, u, d;
      0, 0, -e, u]

/-- Four skew directions mixing the two pair blocks. -/
def realSchurPairPairGenerator (p q r s : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -p, -q;
      0, 0, -r, -s;
      p, r, 0, 0;
      q, s, 0, 0]

/-- The upper-right block of the actual infinitesimal conjugation equals
the four-dimensional Sylvester operator whose determinant is the product
of the two complex spectral-gap factors. -/
theorem realSchur_pair_pair_orbit_sylvester
    (x b c u d e p q r s : ℝ) (i : Fin 4) :
    let K := realSchurPairPairGenerator p q r s
    let D := realSchurPairPairDiagonal x b c u d e
    ![(K*D-D*K) 0 2, (K*D-D*K) 0 3,
      (K*D-D*K) 1 2, (K*D-D*K) 1 3] i =
        (realSchurPairPairSylvester x b c u d e).mulVec
          ![p,q,r,s] i := by
  dsimp
  fin_cases i <;>
    simp [realSchurPairPairGenerator, realSchurPairPairDiagonal,
      realSchurPairPairSylvester, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

#print axioms realSchur_pair_pair_orbit_sylvester
end SpectralRadiusUpperTail
