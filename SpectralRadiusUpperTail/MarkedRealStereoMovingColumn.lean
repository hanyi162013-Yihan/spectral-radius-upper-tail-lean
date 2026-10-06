import SpectralRadiusUpperTail.MarkedRealStereoColumnDifferential
import SpectralRadiusUpperTail.MarkedRealStereoScalarAlgebra
import SpectralRadiusUpperTail.MarkedRealStereoCoverage

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

theorem markedRealVector_sum_split (m : ℕ)
    (f : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) :
    (∑ i, f i) = f (markedRealFirstCoordinate m) + ∑ i : Fin m, f ⟨1,i⟩ := by
  have h := markedRealVectorCons_sum m (f (markedRealFirstCoordinate m))
    (fun i => f ⟨1,i⟩) id
  rwa [markedRealVectorCons_reconstruct] at h

/-- The moving first-column differential is conformal, with its exact
scale retained in every dimension. -/
theorem markedRealStereoFrame_moving_column
    (m : ℕ) (u h : Fin m → ℝ) (i : Fin m) :
    ((markedRealStereoFrame m u)ᵀ * fderiv ℝ (markedRealStereoFrame m) u h)
      ⟨1,i⟩ (markedRealFirstCoordinate m) =
      (2/markedRealStereoDenom m u)*h i := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [markedRealVector_sum_split]
  simp only [markedRealStereoFrame_first_complement,
    markedRealStereoFrame_complement_complement,
    markedRealStereoFrame_fderiv_first_first,
    markedRealStereoFrame_fderiv_complement_first]
  exact markedRealStereo_moving_coordinate_algebra m u h i

#print axioms markedRealVector_sum_split
#print axioms markedRealStereoFrame_moving_column
end SpectralRadiusUpperTail
