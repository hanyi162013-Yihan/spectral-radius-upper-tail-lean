import SpectralRadiusUpperTail.MarkedRealStereoMatrixDifferential
import SpectralRadiusUpperTail.MarkedRealTwoBlockGaussianChart

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Full Jacobian of the explicit hemisphere Schur map: the spectral
factor is the complementary characteristic determinant. -/
theorem markedRealStereoEntryMap_fderiv_abs_det (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    |(fderiv ℝ (markedRealStereoEntryMap m) x).det| =
      |(markedRealComplement m x.2.val - markedRealScalar m x.2.val •
        (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        |markedRealStereoAngularJacobian m x.1| := by
  rw [markedRealStereoEntryMap_fderiv_det, abs_mul]
  congr 1
  rw [markedRealOrbitMatrix_det m x.2.val
    (markedRealComplement m x.2.val) (markedRealScalar m x.2.val)
      (by intros; rfl) rfl]

theorem markedRealStereoEntryMap_gaussianWeight (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    realSchurMixedGaussianCoordinateWeight (markedRealTwoBlockSizes m)
      (markedRealStereoEntryMap m x) =
      realMatrixGaussianWeight (RealSchurMixedCoord (markedRealTwoBlockSizes m)) x.2.val := by
  unfold realSchurMixedGaussianCoordinateWeight markedRealStereoEntryMap
  rw [LinearEquiv.symm_apply_apply]
  exact realMatrixGaussianWeight_orthogonal_conjugation _ _ _
    (markedRealStereoNativeFrame_orthogonal m x.1)

#print axioms markedRealStereoEntryMap_fderiv_abs_det
#print axioms markedRealStereoEntryMap_gaussianWeight
end SpectralRadiusUpperTail
