import SpectralRadiusUpperTail.MarkedRealStereoColumnMap
import SpectralRadiusUpperTail.ScalarVectorConeDerivative

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

/-- Positive radius times a stereographic unit column, written in the
same scalar/complement product coordinates on both sides. -/
noncomputable def markedRealStereoConeMap (m : ℕ) (x : ℝ × (Fin m → ℝ)) :
    ℝ × (Fin m → ℝ) :=
  (markedRealVectorProductEquiv m).symm (x.1 • markedRealStereoColumn m x.2)

def markedRealStereoConeSource (m : ℕ) : Set (ℝ × (Fin m → ℝ)) :=
  Set.Ioi 0 ×ˢ {u | u ⬝ᵥ u < 1}

theorem markedRealStereoConeMap_apply (m : ℕ) (x : ℝ × (Fin m → ℝ)) :
    markedRealStereoConeMap m x =
      (x.1 * markedRealStereoFrame m x.2 (markedRealFirstCoordinate m) (markedRealFirstCoordinate m),
       fun i => x.1 * markedRealStereoFrame m x.2 ⟨1,i⟩ (markedRealFirstCoordinate m)) := rfl

theorem markedRealStereoConeMap_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoConeMap m) :=
  (markedRealVectorProductEquiv m).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_fst.smul ((markedRealStereoColumn_contDiff m).comp contDiff_snd))

theorem markedRealStereoConeMap_fderiv (m : ℕ) (x h : ℝ × (Fin m → ℝ)) :
    fderiv ℝ (markedRealStereoConeMap m) x h =
      (markedRealVectorProductEquiv m).symm
        (x.1 • fderiv ℝ (markedRealStereoColumn m) x.2 h.2 +
          h.1 • markedRealStereoColumn m x.2) := by
  have hf : DifferentiableAt ℝ
      (fun y : ℝ × (Fin m → ℝ) => y.1 • markedRealStereoColumn m y.2) x :=
    differentiableAt_fst.smul
      (((markedRealStereoColumn_contDiff m).differentiable (by simp) x.2).comp x
        differentiableAt_snd)
  have hh := (markedRealVectorProductEquiv m).symm.toContinuousLinearEquiv.hasFDerivAt.comp
    x hf.hasFDerivAt
  erw [hh.fderiv]
  change (markedRealVectorProductEquiv m).symm
    (fderiv ℝ (fun y : ℝ × (Fin m → ℝ) => y.1 • markedRealStereoColumn m y.2) x h) = _
  rw [scalar_vector_cone_fderiv _ x h
    ((markedRealStereoColumn_contDiff m).differentiable (by simp) x.2)]

#print axioms markedRealStereoConeMap_apply
#print axioms markedRealStereoConeMap_contDiff
#print axioms markedRealStereoConeMap_fderiv
end SpectralRadiusUpperTail
