import SpectralRadiusUpperTail.MarkedRealStereoMatrixMap
import SpectralRadiusUpperTail.MarkedRealStereoAngularJacobian

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Differentiating the explicit Schur map in its moving orthogonal frame
produces the already verified block tangent map. -/
theorem markedRealStereoMatrixMap_fderiv_rotated (m : ℕ)
    (x v : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    (markedRealStereoNativeFrame m x.1)ᵀ *
        fderiv ℝ (markedRealStereoMatrixMap m) x v *
          markedRealStereoNativeFrame m x.1 =
      realSchurMixedMovingTangentMap (markedRealTwoBlockSizes m) x.2.val
        (markedRealStereoMovingFrame m x.1) v := by
  let s := markedRealTwoBlockSizes m
  let U : RealSchurMixedTangent s → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
    fun y => markedRealStereoNativeFrame m y.1
  let V : RealSchurMixedTangent s → Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
    fun y => (U y)ᵀ
  let Tr := (Matrix.transposeLinearEquiv (RealSchurMixedCoord s)
    (RealSchurMixedCoord s) ℝ ℝ).toContinuousLinearEquiv
  have hU := ((markedRealStereoNativeFrame_contDiff m).differentiable
    (by simp) x.1).hasFDerivAt.comp x
      hasFDerivAt_fst
  have hV : DifferentiableAt ℝ V x :=
    (Tr.hasFDerivAt.comp x hU).differentiableAt
  have hS := (realSchurMixedUpperTangentCLM s).hasFDerivAt (x := x)
  have hVU (y : RealSchurMixedTangent s) : V y * U y = 1 :=
    markedRealStereoNativeFrame_orthogonal m y.1
  have hh := Ginibre.fderiv_conjugation_rotated
    hU.differentiableAt hV hS.differentiableAt hVU v
  erw [hU.fderiv, hS.fderiv] at hh
  exact hh

noncomputable def markedRealStereoRotatedDifferential (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    RealSchurMixedTangent (markedRealTwoBlockSizes m) →ₗ[ℝ]
      RealSchurMixedTangent (markedRealTwoBlockSizes m) :=
  (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).toLinearMap.comp
    (realSchurMixedMovingTangentMap (markedRealTwoBlockSizes m) x.2.val
      (markedRealStereoMovingFrame m x.1))

theorem markedRealStereoRotatedDifferential_output_comp (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    markedRealStereoRotatedDifferential m x =
      (realSchurMixedEntryConjugation (markedRealTwoBlockSizes m)
        (markedRealStereoNativeFrame m x.1)ᵀ (markedRealStereoNativeFrame m x.1)).comp
          (fderiv ℝ (markedRealStereoEntryMap m) x).toLinearMap := by
  apply LinearMap.ext
  intro v
  change realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)
    (realSchurMixedMovingTangentMap (markedRealTwoBlockSizes m) x.2.val
      (markedRealStereoMovingFrame m x.1) v) =
    realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)
      ((markedRealStereoNativeFrame m x.1)ᵀ *
        (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm
          (fderiv ℝ (markedRealStereoEntryMap m) x v) *
        markedRealStereoNativeFrame m x.1)
  rw [markedRealStereoEntryMap_fderiv_apply, LinearEquiv.symm_apply_apply,
    markedRealStereoMatrixMap_fderiv_rotated]

theorem markedRealStereoEntryMap_fderiv_det (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    (fderiv ℝ (markedRealStereoEntryMap m) x).det =
      (realSchurMixedOrbitMatrix (markedRealTwoBlockSizes m) x.2.val).det *
        markedRealStereoAngularJacobian m x.1 := by
  have he : LinearMap.det (markedRealStereoRotatedDifferential m x) =
      (fderiv ℝ (markedRealStereoEntryMap m) x).det := by
    rw [markedRealStereoRotatedDifferential_output_comp, LinearMap.det_comp,
      realSchurMixedEntryConjugation_det_of_inverse _ _ _
        (markedRealStereoNativeFrame_orthogonal m x.1), one_mul]
  rw [← he]
  exact realSchurMixedMovingTangentMap_det _ _ x.2.property _

#print axioms markedRealStereoMatrixMap_fderiv_rotated
#print axioms markedRealStereoRotatedDifferential_output_comp
#print axioms markedRealStereoEntryMap_fderiv_det
end SpectralRadiusUpperTail
