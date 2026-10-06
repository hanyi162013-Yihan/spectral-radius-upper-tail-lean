import SpectralRadiusUpperTail.MarkedRealStereoFrame
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem markedRealStereoFrame_first_positive (m : ℕ) (u : Fin m → ℝ)
    (hu : u ⬝ᵥ u < 1) :
    0 < markedRealStereoFrame m u (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) := by
  rw [markedRealStereoFrame_first_first]
  exact div_pos (by linarith) (markedRealStereoDenom_pos m u)

theorem markedRealStereoFrame_one_add_first (m : ℕ) (u : Fin m → ℝ) :
    1 + markedRealStereoFrame m u (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) =
      2/markedRealStereoDenom m u := by
  rw [markedRealStereoFrame_first_first]
  have hd := (markedRealStereoDenom_pos m u).ne'
  change 1+(1-u ⬝ᵥ u)/(1+u ⬝ᵥ u) = 2/(1+u ⬝ᵥ u)
  change 1+u ⬝ᵥ u ≠ 0 at hd
  field_simp [hd]
  <;> ring

/-- Recover the chart parameter from its marked unit column. -/
theorem markedRealStereoFrame_firstColumn_inverse (m : ℕ) (u : Fin m → ℝ) (i : Fin m) :
    markedRealStereoFrame m u ⟨1,i⟩ (markedRealFirstCoordinate m) /
        (1+markedRealStereoFrame m u (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)) = u i := by
  rw [markedRealStereoFrame_complement_first, markedRealStereoFrame_one_add_first]
  field_simp [(markedRealStereoDenom_pos m u).ne']

theorem markedRealStereoFrame_firstColumn_injective (m : ℕ) :
    Function.Injective (fun u : Fin m → ℝ => fun i =>
      markedRealStereoFrame m u i (markedRealFirstCoordinate m)) := by
  intro u v h
  funext i
  have he := congrArg (fun f : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ =>
    f ⟨1,i⟩/(1+f (markedRealFirstCoordinate m))) h
  exact (markedRealStereoFrame_firstColumn_inverse m u i).symm.trans
    (he.trans (markedRealStereoFrame_firstColumn_inverse m v i))

#print axioms markedRealStereoFrame_first_positive
#print axioms markedRealStereoFrame_one_add_first
#print axioms markedRealStereoFrame_firstColumn_inverse
#print axioms markedRealStereoFrame_firstColumn_injective
end SpectralRadiusUpperTail
