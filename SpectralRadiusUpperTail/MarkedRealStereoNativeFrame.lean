import SpectralRadiusUpperTail.MarkedRealStereoSmooth
import SpectralRadiusUpperTail.MarkedRealStereoInverse

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Reindex the existing angular coordinates by the complementary column. -/
noncomputable def markedRealStereoParameterCLM (m : ℕ) :
    (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun w := fun i => w (markedRealOrbitEquiv m i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem markedRealStereoParameterCLM_injective (m : ℕ) :
    Function.Injective (markedRealStereoParameterCLM m) := by
  intro w v h
  funext q
  obtain ⟨i, rfl⟩ := (markedRealOrbitEquiv m).surjective q
  exact congrFun h i

noncomputable def markedRealStereoNativeFrame (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :=
  markedRealStereoFrame m (markedRealStereoParameterCLM m w)

theorem markedRealStereoNativeFrame_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoNativeFrame m) :=
  (markedRealStereoFrame_contDiff m).comp (markedRealStereoParameterCLM m).contDiff

theorem markedRealStereoNativeFrame_orthogonal (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    (markedRealStereoNativeFrame m w)ᵀ * markedRealStereoNativeFrame m w = 1 :=
  markedRealStereoFrame_orthogonal m _

theorem markedRealStereoNativeFrame_firstColumn_injective (m : ℕ) :
    Function.Injective (fun w => fun i =>
      markedRealStereoNativeFrame m w i (markedRealFirstCoordinate m)) := by
  intro w v h
  apply markedRealStereoParameterCLM_injective m
  exact markedRealStereoFrame_firstColumn_injective m h

/-- A dimension-independent domain covering one open hemisphere. -/
def markedRealStereoSource (m : ℕ) :
    Set (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :=
  {w | markedRealStereoParameterCLM m w ⬝ᵥ markedRealStereoParameterCLM m w < 1}

theorem markedRealStereoNativeFrame_first_positive (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (hw : w ∈ markedRealStereoSource m) :
    0 < markedRealStereoNativeFrame m w
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) :=
  markedRealStereoFrame_first_positive m _ hw

theorem markedRealStereoNativeFrame_fderiv (m : ℕ)
    (w v : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    fderiv ℝ (markedRealStereoNativeFrame m) w v =
      fderiv ℝ (markedRealStereoFrame m) (markedRealStereoParameterCLM m w)
        (markedRealStereoParameterCLM m v) := by
  have hh := ((markedRealStereoFrame_differentiable m
    (markedRealStereoParameterCLM m w)).hasFDerivAt).comp w
      (markedRealStereoParameterCLM m).hasFDerivAt
  rw [show fderiv ℝ (markedRealStereoNativeFrame m) w =
    (fderiv ℝ (markedRealStereoFrame m) (markedRealStereoParameterCLM m w)).comp
      (markedRealStereoParameterCLM m) from hh.fderiv]
  rfl

#print axioms markedRealStereoParameterCLM_injective
#print axioms markedRealStereoNativeFrame_contDiff
#print axioms markedRealStereoNativeFrame_orthogonal
#print axioms markedRealStereoNativeFrame_firstColumn_injective
#print axioms markedRealStereoNativeFrame_first_positive
#print axioms markedRealStereoNativeFrame_fderiv
end SpectralRadiusUpperTail
