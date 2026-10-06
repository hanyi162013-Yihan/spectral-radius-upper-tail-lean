import SpectralRadiusUpperTail.MarkedRealStereoMovingColumn
import SpectralRadiusUpperTail.MarkedRealStereoNativeFrame

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def markedRealStereoMovingFrame (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) →ₗ[ℝ]
      Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ where
  toFun v := (markedRealStereoNativeFrame m w)ᵀ *
    fderiv ℝ (markedRealStereoNativeFrame m) w v
  map_add' v u := by rw [map_add, Matrix.mul_add]
  map_smul' a v := by rw [map_smul, Matrix.mul_smul]; rfl

theorem markedRealStereoMovingFrame_lower (m : ℕ)
    (w v : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    realSchurMixedLowerProjection (markedRealTwoBlockSizes m)
        (markedRealStereoMovingFrame m w v) =
      (2/markedRealStereoDenom m (markedRealStereoParameterCLM m w)) • v := by
  funext q
  obtain ⟨i, rfl⟩ := (markedRealOrbitEquiv m).surjective q
  change ((markedRealStereoNativeFrame m w)ᵀ *
      fderiv ℝ (markedRealStereoNativeFrame m) w v)
        ⟨1,i⟩ (markedRealFirstCoordinate m) = _
  rw [markedRealStereoNativeFrame_fderiv]
  exact markedRealStereoFrame_moving_column m _ _ i

noncomputable def markedRealStereoAngularJacobian (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) : ℝ :=
  LinearMap.det ((-(realSchurMixedLowerProjection
    (markedRealTwoBlockSizes m)).toLinearMap).comp (markedRealStereoMovingFrame m w))

/-- Exact angular determinant, including its orientation sign. -/
theorem markedRealStereoAngularJacobian_eq (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    markedRealStereoAngularJacobian m w =
      (-(2/markedRealStereoDenom m (markedRealStereoParameterCLM m w)))^m := by
  have he : (-(realSchurMixedLowerProjection
      (markedRealTwoBlockSizes m)).toLinearMap).comp (markedRealStereoMovingFrame m w) =
      (-(2/markedRealStereoDenom m (markedRealStereoParameterCLM m w))) •
        (LinearMap.id : (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) →ₗ[ℝ]
          (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)) := by
    apply LinearMap.ext
    intro v
    change -realSchurMixedLowerProjection (markedRealTwoBlockSizes m)
      (markedRealStereoMovingFrame m w v) = _
    simp only [markedRealStereoMovingFrame_lower, LinearMap.smul_apply,
      LinearMap.id_apply, neg_smul]
  have hc : Fintype.card (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m)) = m := by
    simpa using (Fintype.card_congr (markedRealOrbitEquiv m)).symm
  unfold markedRealStereoAngularJacobian
  rw [he, LinearMap.det_smul, LinearMap.det_id, mul_one,
    Module.finrank_fintype_fun_eq_card, hc]

theorem markedRealStereoAngularJacobian_abs (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :
    |markedRealStereoAngularJacobian m w| =
      (2/markedRealStereoDenom m (markedRealStereoParameterCLM m w))^m := by
  rw [markedRealStereoAngularJacobian_eq, abs_pow, abs_neg,
    abs_of_pos (div_pos (by norm_num) (markedRealStereoDenom_pos m _))]

#print axioms markedRealStereoMovingFrame_lower
#print axioms markedRealStereoAngularJacobian_eq
#print axioms markedRealStereoAngularJacobian_abs
end SpectralRadiusUpperTail
