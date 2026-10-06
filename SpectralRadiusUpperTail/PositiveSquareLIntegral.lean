import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

theorem positive_square_lintegral (f : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (0 : ℝ), f u)=
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (2*y)*f (y^2) := by
  have himage : (fun y : ℝ => y^2) '' Ioi (0 : ℝ)=Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro ⟨y,hy,rfl⟩
      change 0 < y at hy
      change 0 < y^2
      exact sq_pos_of_pos hy
    · intro hu
      exact ⟨Real.sqrt u,Real.sqrt_pos.mpr hu,Real.sq_sqrt hu.le⟩
  have hinj : InjOn (fun y : ℝ => y^2) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    change x^2=y^2 at hxy
    nlinarith
  have hd (y : ℝ) (hy : y ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun x : ℝ => x^2) (2*y) (Ioi (0 : ℝ)) y := by
    convert! (hasDerivAt_pow 2 y).hasDerivWithinAt (s := Ioi (0 : ℝ)) using 1
    norm_num
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj f
  rw [himage] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro y hy
  change 0 < y at hy
  dsimp only
  rw [abs_of_pos (by positivity : 0 < 2*y)]

#print axioms positive_square_lintegral
end SpectralRadiusUpperTail
