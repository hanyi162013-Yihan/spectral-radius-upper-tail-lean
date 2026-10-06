import SpectralRadiusUpperTail.MarkedRealStereoFrame
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem markedRealStereo_complement_sum (m : ℕ) (u x : Fin m → ℝ)
    (c : ℝ) (i : Fin m) :
    (∑ j, ((1 : Matrix (Fin m) (Fin m) ℝ) j i - c*(u j*u i))*x j) =
      x i - c*u i*(u ⬝ᵥ x) := by
  have he (j : Fin m) :
      ((1 : Matrix (Fin m) (Fin m) ℝ) j i - c*(u j*u i))*x j =
      (1 : Matrix (Fin m) (Fin m) ℝ) j i*x j - c*u i*(u j*x j) := by ring
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Matrix.one_apply, dotProduct]

theorem markedRealStereo_derivative_dot (m : ℕ) (u h : Fin m → ℝ) (d : ℝ) :
    u ⬝ᵥ (fun j => 2*h j/d - 4*u j*(u ⬝ᵥ h)/d^2) =
      2*(u ⬝ᵥ h)/d - 4*(u ⬝ᵥ u)*(u ⬝ᵥ h)/d^2 := by
  have he (j : Fin m) :
      u j*(2*h j/d - 4*u j*(u ⬝ᵥ h)/d^2) =
      (2/d)*(u j*h j) - (4*(u ⬝ᵥ h)/d^2)*(u j*u j) := by ring
  change (∑ j, u j*(2*h j/d - 4*u j*(u ⬝ᵥ h)/d^2)) = _
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (2/d)*(u ⬝ᵥ h) - (4*(u ⬝ᵥ h)/d^2)*(u ⬝ᵥ u) = _
  ring

/-- The cancellation in the moving first-column derivative, kept separate
from the matrix differential and its coordinate instances. -/
theorem markedRealStereo_moving_coordinate_algebra
    (m : ℕ) (u h : Fin m → ℝ) (i : Fin m) :
    -(2*u i/markedRealStereoDenom m u)*
        (-4*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2) +
      (∑ j, ((1 : Matrix (Fin m) (Fin m) ℝ) j i -
          (2/markedRealStereoDenom m u)*(u j*u i))*
        (2*h j/markedRealStereoDenom m u -
          4*u j*(u ⬝ᵥ h)/(markedRealStereoDenom m u)^2)) =
      (2/markedRealStereoDenom m u)*h i := by
  rw [markedRealStereo_complement_sum, markedRealStereo_derivative_dot]
  have hd : 1+u ⬝ᵥ u ≠ 0 := (markedRealStereoDenom_pos m u).ne'
  unfold markedRealStereoDenom
  field_simp [hd]
  <;> ring

#print axioms markedRealStereo_complement_sum
#print axioms markedRealStereo_derivative_dot
#print axioms markedRealStereo_moving_coordinate_algebra
end SpectralRadiusUpperTail
