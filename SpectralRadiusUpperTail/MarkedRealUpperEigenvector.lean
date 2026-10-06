import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart
import SpectralRadiusUpperTail.MarkedRealEigenlineBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The distinguished first column of a block-upper `(1,m)` matrix is
an eigenvector for the marked scalar. -/
theorem markedRealUpper_firstBasis_eigenvector
    (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0) :
    S.mulVecLin (Pi.single (markedRealFirstCoordinate m) 1) =
      markedRealScalar m S • Pi.single (markedRealFirstCoordinate m) 1 := by
  ext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Pi.smul_apply]
  by_cases hi : i = markedRealFirstCoordinate m
  · subst i
    simp [markedRealScalar]
  · have hi1 : i.1 = 1 := by
      by_contra h
      have h0 : i.1 = 0 := by omega
      apply hi
      cases i with
      | mk k j =>
        have hk : k = 0 := h0
        subst k
        have hj : j = markedRealZeroCoordinate m := by
          have hjlt : j.val < 1 := by
            simpa [markedRealTwoBlockSizes] using j.isLt
          apply Fin.ext
          simp [markedRealZeroCoordinate]
        subst j
        rfl
    have hz : S i (markedRealFirstCoordinate m) = 0 :=
      (realSchurMixed_blockTriangular_iff_lower_zero _ _).mpr hS
        (by simp [hi1])
    simp [hi, hz]

/-- Orthogonal conjugation transports the distinguished eigenvector
without changing its real eigenvalue. -/
theorem markedRealUpper_rotatedFirstColumn_eigenvector
    (m : ℕ)
    (S Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hS : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0)
    (hQ : Qᵀ*Q=1) :
    (Q*S*Qᵀ).mulVecLin
      (Q.mulVecLin (Pi.single (markedRealFirstCoordinate m) 1)) =
        markedRealScalar m S •
          Q.mulVecLin (Pi.single (markedRealFirstCoordinate m) 1) := by
  have hmat : (Q*S*Qᵀ)*Q = Q*S := by
    simp only [Matrix.mul_assoc]
    rw [hQ, Matrix.mul_one]
  calc
    (Q*S*Qᵀ).mulVecLin
        (Q.mulVecLin (Pi.single (markedRealFirstCoordinate m) 1)) =
      ((Q*S*Qᵀ)*Q).mulVecLin
        (Pi.single (markedRealFirstCoordinate m) 1) := by
          simp only [Matrix.mulVecLin_mul, LinearMap.comp_apply]
    _ = (Q*S).mulVecLin (Pi.single (markedRealFirstCoordinate m) 1) := by
      rw [hmat]
    _ = Q.mulVecLin
        (S.mulVecLin (Pi.single (markedRealFirstCoordinate m) 1)) := by
          simp only [Matrix.mulVecLin_mul, LinearMap.comp_apply]
    _ = _ := by
      rw [markedRealUpper_firstBasis_eigenvector m S hS, map_smul]

#print axioms markedRealUpper_firstBasis_eigenvector
#print axioms markedRealUpper_rotatedFirstColumn_eigenvector
end SpectralRadiusUpperTail
