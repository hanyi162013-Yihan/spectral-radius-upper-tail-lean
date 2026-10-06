import SpectralRadiusUpperTail.MarkedRealTwoBlockJacobian
import SpectralRadiusUpperTail.RealSchurMixedJacobianEverywhere
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- At every point of a two-block Schur chart, the full coordinate
Jacobian factors into the complementary characteristic determinant and
the angular-coordinate Jacobian. -/
theorem markedRealTwoBlock_fderiv_det
    (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (H : Matrix (Fin m) (Fin m) ℝ) (x : ℝ)
    (hH : ∀ i j, (T+t.2.val) ⟨1,i⟩ ⟨1,j⟩ = H i j)
    (hx : (T+t.2.val) ⟨0,markedRealZeroCoordinate m⟩
      ⟨0,markedRealZeroCoordinate m⟩ = x) :
    (fderiv ℝ (realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) T) t).det =
      (H-x • (1 : Matrix (Fin m) (Fin m) ℝ)).det *
        realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1 := by
  rw [realSchurMixedEntryCoordinates_fderiv_det_everywhere
    (markedRealTwoBlockSizes m) T hT t,
    markedRealOrbitMatrix_det m (T+t.2.val) H x hH hx]

theorem markedRealTwoBlock_fderiv_abs_det
    (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hT : realSchurMixedLowerProjection (markedRealTwoBlockSizes m) T = 0)
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m))
    (H : Matrix (Fin m) (Fin m) ℝ) (x : ℝ)
    (hH : ∀ i j, (T+t.2.val) ⟨1,i⟩ ⟨1,j⟩ = H i j)
    (hx : (T+t.2.val) ⟨0,markedRealZeroCoordinate m⟩
      ⟨0,markedRealZeroCoordinate m⟩ = x) :
    |(fderiv ℝ (realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) T) t).det| =
      |(H-x • (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1| := by
  rw [markedRealTwoBlock_fderiv_det m T hT t H x hH hx, abs_mul]

#print axioms markedRealTwoBlock_fderiv_det
#print axioms markedRealTwoBlock_fderiv_abs_det
end SpectralRadiusUpperTail
