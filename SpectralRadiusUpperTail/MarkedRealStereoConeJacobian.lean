import SpectralRadiusUpperTail.MarkedRealStereoConeMap
import SpectralRadiusUpperTail.MarkedRealVectorRotation

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem markedRealStereoConeMap_fderiv_rotated (m : ℕ)
    (x h : ℝ × (Fin m → ℝ)) :
    markedRealVectorRotation m (markedRealStereoFrame m x.2)ᵀ
      (fderiv ℝ (markedRealStereoConeMap m) x h) =
      (h.1, (x.1 * (2/markedRealStereoDenom m x.2)) • h.2) := by
  rw [markedRealVectorRotation_apply, markedRealStereoConeMap_fderiv,
    LinearEquiv.apply_symm_apply, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, markedRealStereoColumn_fderiv_rotated,
    markedRealStereoColumn_rotated]
  change (markedRealVectorProductEquiv m).symm
    (x.1 • markedRealVectorProductEquiv m (0, (2/markedRealStereoDenom m x.2) • h.2) +
      h.1 • markedRealVectorProductEquiv m (1, (0 : Fin m → ℝ))) = _
  rw [← map_smul, ← map_smul, ← map_add, LinearEquiv.symm_apply_apply]
  ext i <;> simp [smul_smul]

theorem markedRealStereoConeMap_fderiv_rotated_linear (m : ℕ)
    (x : ℝ × (Fin m → ℝ)) :
    (markedRealVectorRotation m (markedRealStereoFrame m x.2)ᵀ).comp
      (fderiv ℝ (markedRealStereoConeMap m) x).toLinearMap =
      LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        ((x.1 * (2/markedRealStereoDenom m x.2)) •
          (LinearMap.id : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) := by
  apply LinearMap.ext
  intro h
  exact markedRealStereoConeMap_fderiv_rotated m x h

theorem markedRealStereoConeMap_fderiv_abs_det (m : ℕ)
    (x : ℝ × (Fin m → ℝ)) (hx : 0 ≤ x.1) :
    |(fderiv ℝ (markedRealStereoConeMap m) x).det| =
      x.1^m * (2/markedRealStereoDenom m x.2)^m := by
  have hd := congrArg LinearMap.det (markedRealStereoConeMap_fderiv_rotated_linear m x)
  simp only [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id,
    LinearMap.det_smul, one_mul, mul_one, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hd
  have ha := congrArg abs hd
  rw [abs_mul, markedRealVectorRotation_abs_det_of_orthogonal m _
    (markedRealStereoFrame_orthogonal m x.2), one_mul] at ha
  rw [abs_of_nonneg (pow_nonneg (mul_nonneg hx
    (div_nonneg (by norm_num) (markedRealStereoDenom_pos m x.2).le)) _), mul_pow] at ha
  exact ha

#print axioms markedRealStereoConeMap_fderiv_rotated
#print axioms markedRealStereoConeMap_fderiv_rotated_linear
#print axioms markedRealStereoConeMap_fderiv_abs_det
end SpectralRadiusUpperTail
