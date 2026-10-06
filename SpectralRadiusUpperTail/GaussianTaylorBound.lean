import SpectralRadiusUpperTail.SegmentTaylor
import SpectralRadiusUpperTail.GaussianLineDerivatives
import SpectralRadiusUpperTail.GaussianRadialBounds
import Mathlib.Tactic.GCongr

namespace SpectralRadiusUpperTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gaussianThirdConstant (a : ℝ) : ℝ :=
  3*(2/a)^2*(1+a)+(2/a)^3*(1+2*a^2)

lemma gaussianThirdConstant_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ gaussianThirdConstant a := by unfold gaussianThirdConstant; positivity

/-- Translation-uniform third-derivative bound for the actual Gaussian kernel,
with cubic dependence on the displacement. -/
theorem gaussianLine_third_bound (a : ℝ) (ha : 0 < a) (s h : E) (t : ℝ) :
    |gaussianLineThird a s h t| ≤ gaussianThirdConstant a*‖h‖^3 := by
  let r := ‖s+t • h‖
  let p := gaussianLineSlope a s h t
  let g := gaussianLine a s h t
  have hg : 0 ≤ g := Real.exp_nonneg _
  have hcoef : |(-2/a : ℝ)| = 2/a := by
    rw [abs_div, abs_of_pos ha]
    norm_num
  have hp : |p| ≤ (2/a)*r*‖h‖ := by
    dsimp [p, gaussianLineSlope]
    rw [abs_mul, hcoef]
    calc
      _ ≤ (2/a)*(‖s+t • h‖*‖h‖) := mul_le_mul_of_nonneg_left
        (abs_real_inner_le_norm _ _) (by positivity)
      _ = _ := by ring
  have hb : |3*((-2/a)*‖h‖^2)*p+p^3| ≤
      3*((2/a)*‖h‖^2)*|p|+|p|^3 := by
    have hh := abs_add_le (3*((-2/a)*‖h‖^2)*p) (p^3)
    simpa only [abs_mul, abs_pow, abs_of_nonneg (norm_nonneg h),
      hcoef, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] using hh
  have hpoly : 3*((2/a)*‖h‖^2)*|p|+|p|^3 ≤
      3*((2/a)*‖h‖^2)*((2/a)*r*‖h‖)+((2/a)*r*‖h‖)^3 := by
    gcongr
  have hr := gaussian_radial_odd_bounds a r ha
  change |(3*((-2/a)*‖h‖^2)*p+p^3)*g| ≤ _
  rw [abs_mul, abs_of_nonneg hg]
  calc
    _ ≤ (3*((2/a)*‖h‖^2)*|p|+|p|^3)*g := mul_le_mul_of_nonneg_right hb hg
    _ ≤ (3*((2/a)*‖h‖^2)*((2/a)*r*‖h‖)+((2/a)*r*‖h‖)^3)*g :=
      mul_le_mul_of_nonneg_right hpoly hg
    _ = ‖h‖^3*(3*(2/a)^2*(r*g)+(2/a)^3*(r^3*g)) := by ring
    _ ≤ ‖h‖^3*(3*(2/a)^2*(1+a)+(2/a)^3*(1+2*a^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hr.1 (by positivity)
      · exact mul_le_mul_of_nonneg_left hr.2 (by positivity)
    _ = _ := by unfold gaussianThirdConstant; ring

/-- A concrete second-order expansion of the Gaussian soft weight, with a
uniform cubic remainder. All derivatives and their bounds are proved above. -/
theorem gaussian_quadratic_remainder (a : ℝ) (ha : 0 < a) (s h : E) :
    |Real.exp (-‖s+h‖^2/a) -
      (Real.exp (-‖s‖^2/a)+((-2/a)*inner ℝ s h)*Real.exp (-‖s‖^2/a)+
        (1/2)*(((-2/a)*‖h‖^2+((-2/a)*inner ℝ s h)^2)*Real.exp (-‖s‖^2/a)))|
      ≤ (gaussianThirdConstant a/2)*‖h‖^3 := by
  have hh := segment_quadratic_remainder (gaussianLine a s h)
    (gaussianLineFirst a s h) (gaussianLineSecond a s h) (gaussianLineThird a s h)
    (gaussianThirdConstant a*‖h‖^3)
    (mul_nonneg (gaussianThirdConstant_nonneg a ha) (by positivity))
    (gaussianLine_deriv a s h) (gaussianLine_first_deriv a s h)
    (gaussianLine_second_deriv a s h) (fun t _ => gaussianLine_third_bound a ha s h t)
  have he : gaussianThirdConstant a*‖h‖^3/2 = (gaussianThirdConstant a/2)*‖h‖^3 := by ring
  simpa only [gaussianLine, gaussianLineFirst, gaussianLineSecond, gaussianLineSlope,
    zero_smul, one_smul, add_zero, he] using hh

#print axioms gaussianLine_third_bound
#print axioms gaussian_quadratic_remainder
end SpectralRadiusUpperTail
