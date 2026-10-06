import SpectralRadiusUpperTail.MarkedRealVectorProductEquiv
import Mathlib.LinearAlgebra.Determinant

namespace SpectralRadiusUpperTail
open scoped Matrix

noncomputable def markedRealVectorRotation (m : ℕ)
    (Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) :
    (ℝ × (Fin m → ℝ)) →ₗ[ℝ] (ℝ × (Fin m → ℝ)) :=
  (markedRealVectorProductEquiv m).symm.toLinearMap.comp
    ((Matrix.toLin' Q).comp (markedRealVectorProductEquiv m).toLinearMap)

theorem markedRealVectorRotation_apply (m : ℕ)
    (Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (x : ℝ × (Fin m → ℝ)) :
    markedRealVectorRotation m Q x =
      (markedRealVectorProductEquiv m).symm (Q *ᵥ markedRealVectorProductEquiv m x) := by
  change (markedRealVectorProductEquiv m).symm (Matrix.toLin' Q
    (markedRealVectorProductEquiv m x)) = _
  rw [Matrix.toLin'_apply]

theorem markedRealVectorRotation_det (m : ℕ)
    (Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) :
    LinearMap.det (markedRealVectorRotation m Q) = Q.det := by
  unfold markedRealVectorRotation
  simpa only [LinearEquiv.symm_symm, LinearMap.det_toLin'] using
    LinearMap.det_conj (Matrix.toLin' Q) (markedRealVectorProductEquiv m).symm

theorem markedRealVectorRotation_abs_det_of_orthogonal (m : ℕ)
    (Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hQ : Qᵀ*Q=1) :
    |LinearMap.det (markedRealVectorRotation m Qᵀ)| = 1 := by
  rw [markedRealVectorRotation_det, Matrix.det_transpose]
  have hd : Q.det*Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  have hs : |Q.det|^2 = 1 := by rw [sq_abs, pow_two, hd]
  nlinarith [abs_nonneg Q.det]

#print axioms markedRealVectorRotation_apply
#print axioms markedRealVectorRotation_det
#print axioms markedRealVectorRotation_abs_det_of_orthogonal
end SpectralRadiusUpperTail
