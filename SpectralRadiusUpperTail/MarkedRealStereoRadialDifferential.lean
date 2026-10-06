import SpectralRadiusUpperTail.MarkedRealStereoMovingColumn

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

theorem markedRealStereo_moving_first_algebra (m : ℕ) (u h : Fin m → ℝ) :
    ((1-u ⬝ᵥ u)/markedRealStereoDenom m u)*
        (-4*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2) +
      (∑ j, (2*u j/markedRealStereoDenom m u)*
        (2*h j/markedRealStereoDenom m u -
          4*u j*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2)) = 0 := by
  have hs : (∑ j, (2*u j/markedRealStereoDenom m u)*
      (2*h j/markedRealStereoDenom m u -
        4*u j*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2)) =
      (2/markedRealStereoDenom m u)*
        (u ⬝ᵥ (fun j => 2*h j/markedRealStereoDenom m u -
          4*u j*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2)) := by
    change _ = (2/markedRealStereoDenom m u)*
      (∑ j, u j*(2*h j/markedRealStereoDenom m u -
        4*u j*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, markedRealStereo_derivative_dot]
  have hd : 1+u ⬝ᵥ u ≠ 0 := (markedRealStereoDenom_pos m u).ne'
  unfold markedRealStereoDenom
  field_simp [hd]
  <;> ring

/-- The first component of the moving column derivative vanishes:
the derivative is tangent to the unit sphere. -/
theorem markedRealStereoFrame_moving_first (m : ℕ) (u h : Fin m → ℝ) :
    ((markedRealStereoFrame m u)ᵀ * fderiv ℝ (markedRealStereoFrame m) u h)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) = 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [markedRealVector_sum_split]
  simp only [markedRealStereoFrame_first_first,
    markedRealStereoFrame_complement_first,
    markedRealStereoFrame_fderiv_first_first,
    markedRealStereoFrame_fderiv_complement_first]
  exact markedRealStereo_moving_first_algebra m u h

#print axioms markedRealStereo_moving_first_algebra
#print axioms markedRealStereoFrame_moving_first
end SpectralRadiusUpperTail
