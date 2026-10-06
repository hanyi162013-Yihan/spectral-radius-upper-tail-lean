import SpectralRadiusUpperTail.MarkedRealTwoBlockOrbit
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- In the two-block chart, the angular Jacobian is the characteristic
matrix of the complementary block at the marked real eigenvalue. -/
theorem markedRealOrbitMatrix_reindex (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (H : Matrix (Fin m) (Fin m) ℝ) (x : ℝ)
    (hH : ∀ i j, T ⟨1, i⟩ ⟨1, j⟩ = H i j)
    (hx : T ⟨0, markedRealZeroCoordinate m⟩
      ⟨0, markedRealZeroCoordinate m⟩ = x) :
    Matrix.reindex (markedRealOrbitEquiv m).symm (markedRealOrbitEquiv m).symm
      (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T) =
      H - x • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  ext i j
  change realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T
      (markedRealOrbitEquiv m i) (markedRealOrbitEquiv m j) =
      (H - x • (1 : Matrix (Fin m) (Fin m) ℝ)) i j
  rw [markedRealOrbitEquiv_apply, markedRealOrbitEquiv_apply]
  rw [realSchurMixedOrbitMatrix_diagonal]
  simp only [realSchurMixedSylvester, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  simp [hH i j, hx]

theorem markedRealOrbitMatrix_det (m : ℕ)
    (T : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (H : Matrix (Fin m) (Fin m) ℝ) (x : ℝ)
    (hH : ∀ i j, T ⟨1, i⟩ ⟨1, j⟩ = H i j)
    (hx : T ⟨0, markedRealZeroCoordinate m⟩
      ⟨0, markedRealZeroCoordinate m⟩ = x) :
    (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) T).det =
      (H - x • (1 : Matrix (Fin m) (Fin m) ℝ)).det := by
  rw [← Matrix.det_reindex_self (markedRealOrbitEquiv m).symm]
  rw [markedRealOrbitMatrix_reindex m T H x hH hx]

#print axioms markedRealOrbitMatrix_reindex
#print axioms markedRealOrbitMatrix_det
end SpectralRadiusUpperTail
