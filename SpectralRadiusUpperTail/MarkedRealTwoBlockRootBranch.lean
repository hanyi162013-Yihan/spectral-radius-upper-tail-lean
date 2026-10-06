import SpectralRadiusUpperTail.MarkedRealTwoBlockRegular
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- In a marked two-block Schur representation, the full characteristic
polynomial splits into the marked linear factor and the complementary
characteristic polynomial. -/
theorem markedRealTwoBlock_charpoly_factor
    (m : ℕ) (hm : 0 < m)
    (T Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hQ : Qᵀ*Q=1) :
    (Q*T*Qᵀ).charpoly =
      (Polynomial.X - Polynomial.C (markedRealScalar m T)) *
        (markedRealComplement m T).charpoly := by
  rw [realMatrixOrthogonalConjugation_charpoly _ Q T hQ,
    realSchurMixed_blockUpper_charpoly
      (markedRealTwoBlockSizes m)
      (by intro i; fin_cases i <;> simp [markedRealTwoBlockSizes, hm])
      T hT, Fin.prod_univ_two]
  have h0 :
      realSchurMixedDiagonalMatrix (markedRealTwoBlockSizes m) T 0 =
        Matrix.scalar (Fin 1) (markedRealScalar m T) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [realSchurMixedDiagonalMatrix, Matrix.scalar_apply,
      markedRealTwoBlockSizes, markedRealScalar, markedRealZeroCoordinate]
  have h1 :
      realSchurMixedDiagonalMatrix (markedRealTwoBlockSizes m) T 1 =
        markedRealComplement m T := by
    rfl
  rw [realSchurMixedDiagonalMatrix_charpoly,
    realSchurMixedDiagonalMatrix_charpoly, h0, h1,
    realSchurScalar_charpoly]

/-- If the complementary block does not have the proposed real root,
the marked scalar is the unique root in this local Schur branch. -/
theorem markedRealTwoBlock_root_eq_scalar_of_complement_ne
    (m : ℕ) (hm : 0 < m)
    (T Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hQ : Qᵀ*Q=1) (x : ℝ)
    (hroot : (Q*T*Qᵀ).charpoly.IsRoot x)
    (hcomp : (markedRealComplement m T).charpoly.eval x ≠ 0) :
    x = markedRealScalar m T := by
  have heval := hroot
  rw [Polynomial.IsRoot, markedRealTwoBlock_charpoly_factor m hm T Q hT hQ,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at heval
  exact sub_eq_zero.mp ((mul_eq_zero.mp heval).resolve_right hcomp)

/-- The same factorization holds throughout the genuine local chart,
not only at its center. -/
theorem markedRealTwoBlock_rotatedChart_charpoly_factor
    (m : ℕ) (hm : 0 < m)
    (T Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hQ : Qᵀ*Q=1)
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    (Q*(realSchurMixedExpCoordinates (markedRealTwoBlockSizes m) T t)*Qᵀ).charpoly =
      (Polynomial.X - Polynomial.C (markedRealScalar m (T+t.2.val))) *
        (markedRealComplement m (T+t.2.val)).charpoly := by
  rw [realMatrixOrthogonalConjugation_charpoly _ Q _ hQ,
    realSchurMixedExpCoordinates_eq_conjugation]
  have hupper :
      realSchurMixedLowerProjection (markedRealTwoBlockSizes m) (T+t.2.val) = 0 := by
    rw [map_add, hT, zero_add]
    exact t.2.property
  exact markedRealTwoBlock_charpoly_factor m hm (T+t.2.val)
    (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) t.1)
    hupper (realSchurMixedAngularFrame_orthogonal _ _)

/-- In a regular marked chart, a root that stays away from the
complementary spectrum has the chart's scalar coordinate. -/
theorem markedRealTwoBlock_rotatedChart_root_unique
    (m : ℕ) (hm : 0 < m)
    (T Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (hQ : Qᵀ*Q=1)
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (x : ℝ)
    (hroot :
      (Q*(realSchurMixedExpCoordinates (markedRealTwoBlockSizes m) T t)*Qᵀ).charpoly.IsRoot x)
    (hcomp : (markedRealComplement m (T+t.2.val)).charpoly.eval x ≠ 0) :
    x = markedRealScalar m (T+t.2.val) := by
  rw [Polynomial.IsRoot,
    markedRealTwoBlock_rotatedChart_charpoly_factor m hm T Q hT hQ t,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hroot
  exact sub_eq_zero.mp ((mul_eq_zero.mp hroot).resolve_right hcomp)

#print axioms markedRealTwoBlock_charpoly_factor
#print axioms markedRealTwoBlock_root_eq_scalar_of_complement_ne
#print axioms markedRealTwoBlock_rotatedChart_charpoly_factor
#print axioms markedRealTwoBlock_rotatedChart_root_unique
end SpectralRadiusUpperTail
