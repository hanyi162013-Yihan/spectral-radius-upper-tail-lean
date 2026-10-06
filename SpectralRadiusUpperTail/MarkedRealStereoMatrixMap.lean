import SpectralRadiusUpperTail.MarkedRealStereoNativeFrame
import SpectralRadiusUpperTail.RealSchurMixedJacobianEverywhere

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The explicit marked-real Schur map in the existing lower/upper
coordinate space. The angular variable ranges over an entire hemisphere. -/
noncomputable def markedRealStereoMatrixMap (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :=
  markedRealStereoNativeFrame m x.1 * x.2.val *
    (markedRealStereoNativeFrame m x.1)ᵀ

noncomputable def markedRealStereoEntryMap (m : ℕ)
    (x : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :=
  realSchurMixedEntryEquiv (markedRealTwoBlockSizes m) (markedRealStereoMatrixMap m x)

theorem markedRealStereoMatrixMap_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoMatrixMap m) := by
  let s := markedRealTwoBlockSizes m
  let Tr := (Matrix.transposeLinearEquiv (RealSchurMixedCoord s)
    (RealSchurMixedCoord s) ℝ ℝ).toContinuousLinearEquiv
  have hQ : ContDiff ℝ ⊤ (fun x : RealSchurMixedTangent s =>
      markedRealStereoNativeFrame m x.1) :=
    (markedRealStereoNativeFrame_contDiff m).comp contDiff_fst
  have hQt : ContDiff ℝ ⊤ (fun x : RealSchurMixedTangent s =>
      (markedRealStereoNativeFrame m x.1)ᵀ) := Tr.contDiff.comp hQ
  exact (hQ.mul (realSchurMixedUpperTangentCLM s).contDiff).mul hQt

theorem markedRealStereoEntryMap_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoEntryMap m) :=
  (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.contDiff.comp
    (markedRealStereoMatrixMap_contDiff m)

theorem markedRealStereoMatrixMap_differentiable (m : ℕ) :
    Differentiable ℝ (markedRealStereoMatrixMap m) :=
  (markedRealStereoMatrixMap_contDiff m).differentiable (by simp)

theorem markedRealStereoEntryMap_differentiable (m : ℕ) :
    Differentiable ℝ (markedRealStereoEntryMap m) :=
  (markedRealStereoEntryMap_contDiff m).differentiable (by simp)

theorem markedRealStereoEntryMap_fderiv_apply (m : ℕ)
    (x v : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    fderiv ℝ (markedRealStereoEntryMap m) x v =
      realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)
        (fderiv ℝ (markedRealStereoMatrixMap m) x v) := by
  have hh := (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.hasFDerivAt.comp
    x (markedRealStereoMatrixMap_differentiable m x).hasFDerivAt
  rw [show fderiv ℝ (markedRealStereoEntryMap m) x =
    (realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fderiv ℝ (markedRealStereoMatrixMap m) x) from hh.fderiv]
  rfl

#print axioms markedRealStereoMatrixMap_contDiff
#print axioms markedRealStereoEntryMap_contDiff
#print axioms markedRealStereoMatrixMap_differentiable
#print axioms markedRealStereoEntryMap_differentiable
#print axioms markedRealStereoEntryMap_fderiv_apply
end SpectralRadiusUpperTail
