import SpectralRadiusUpperTail.GaussianDirectionalDerivatives
import SpectralRadiusUpperTail.GaussianRadialBounds
import SpectralRadiusUpperTail.SegmentTaylor
import Mathlib.Tactic.GCongr

namespace SpectralRadiusUpperTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def gaussianDirectionalThirdConstant (a : ℝ) : ℝ :=
  3*(2/a)^2+6*(2/a)^3*a+2*(2/a)^4*a^2

lemma gaussianDirectionalThirdConstant_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ gaussianDirectionalThirdConstant a := by
  unfold gaussianDirectionalThirdConstant
  positivity

lemma gaussianDirectionalThirdConstant_eq (a : ℝ) (ha : 0 < a) :
    gaussianDirectionalThirdConstant a = 92/a^2 := by
  unfold gaussianDirectionalThirdConstant
  field_simp <;> ring

lemma gaussianDirectional_bound (a : ℝ) (ha : 0 < a) (w z : E) :
    |gaussianDirectional a w z| ≤ (2/a)*(1+a)*‖w‖ := by
  have hcoef : |(-2/a : ℝ)| = 2/a := by
    rw [abs_div, abs_of_pos ha]
    norm_num
  have hr := (gaussian_radial_odd_bounds a ‖z‖ ha).1
  unfold gaussianDirectional
  rw [abs_mul, abs_mul, hcoef, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    _ ≤ (2/a)*(‖z‖*‖w‖)*Real.exp (-‖z‖^2/a) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = ((2/a)*‖w‖)*(‖z‖*Real.exp (-‖z‖^2/a)) := by ring
    _ ≤ ((2/a)*‖w‖)*(1+a) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

/-- The actual third derivative of a first-directional Gaussian test is bounded
uniformly in its argument. This is the required mixed fourth-derivative bound. -/
theorem gaussianDirectional_third_bound (a : ℝ) (ha : 0 < a) (w s h : E) (t : ℝ) :
    |gaussianDirectionalLineThird a w s h t| ≤
      gaussianDirectionalThirdConstant a*‖w‖*‖h‖^3 := by
  let q := 2/a
  let H := ‖h‖
  let W := ‖w‖
  let r := ‖s+t • h‖
  let p := gaussianLineSlope a s h t
  let b := (-2/a)*‖h‖^2
  let u := inner ℝ h w
  let l := inner ℝ (s+t • h) w
  let g := gaussianLine a s h t
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hg : 0 ≤ g := Real.exp_nonneg _
  have hcoef : |(-2/a : ℝ)| = q := by
    dsimp [q]
    rw [abs_div, abs_of_pos ha]
    norm_num
  have hb : |b| = q*H^2 := by
    dsimp only [b, H]
    rw [abs_mul, hcoef, abs_of_nonneg (sq_nonneg _)]
  have hp : |p| ≤ q*r*H := by
    dsimp only [p, gaussianLineSlope]
    rw [abs_mul, hcoef]
    calc
      _ ≤ q*(‖s+t • h‖*‖h‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hq
      _ = _ := by ring
  have hu : |u| ≤ H*W := abs_real_inner_le_norm _ _
  have hl : |l| ≤ r*W := abs_real_inner_le_norm _ _
  have hbp : |b+p^2| ≤ |b|+|p|^2 := by
    convert! abs_add_le b (p^2) using 1 <;> simp only [abs_pow]
  have htp : |3*b*p+p^3| ≤ 3*|b| * |p|+|p|^3 := by
    convert! abs_add_le (3*b*p) (p^3) using 1 <;>
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hpoly : |3*u*(b+p^2)+l*(3*b*p+p^3)| ≤
      3*|u| * (|b|+|p|^2)+|l| * (3*|b| * |p|+|p|^3) := by
    calc
      _ ≤ |3*u*(b+p^2)|+|l*(3*b*p+p^3)| := abs_add_le _ _
      _ = 3*|u| * |b+p^2|+|l| * |3*b*p+p^3| := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ _ := by gcongr
  have h0 : g ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  have h2 : r^2*g ≤ a := by
    simpa [g, gaussianLine, r] using gaussian_radial_even_bound a r ha 1
  have h4 : r^4*g ≤ 2*a^2 := by
    simpa [g, gaussianLine, r, Nat.factorial] using gaussian_radial_even_bound a r ha 2
  have he : gaussianDirectionalLineThird a w s h t =
      (-2/a)*(3*u*(b+p^2)+l*(3*b*p+p^3))*g := by
    dsimp [gaussianDirectionalLineThird, gaussianLineSecond, gaussianLineThird, u, l, b, p, g]
    ring
  rw [he, abs_mul, abs_mul, hcoef, abs_of_nonneg hg]
  calc
    _ ≤ q*(3*|u| * (|b|+|p|^2)+|l| * (3*|b| * |p|+|p|^3))*g := by gcongr
    _ = q*(3*|u| * (q*H^2+|p|^2)+|l| * (3*(q*H^2)*|p|+|p|^3))*g := by rw [hb]
    _ ≤ q*(3*(H*W)*(q*H^2+(q*r*H)^2)+(r*W)*(3*(q*H^2)*(q*r*H)+(q*r*H)^3))*g := by
      gcongr
    _ = W*H^3*(3*q^2*g+6*q^3*(r^2*g)+q^4*(r^4*g)) := by ring
    _ ≤ W*H^3*(3*q^2+6*q^3*a+q^4*(2*a^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hzero := mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 3*q^2)
      have htwo := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 6*q^3)
      have hfour := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ q^4)
      linarith
    _ = _ := by unfold gaussianDirectionalThirdConstant; dsimp [q, H, W]; ring

lemma gaussianDirectional_quadratic_remainder (a : ℝ) (ha : 0 < a) (w s h : E) :
    |gaussianDirectional a w (s+h)-
      (gaussianDirectional a w s+gaussianDirectionalLineFirst a w s h 0+
        (1/2)*gaussianDirectionalLineSecond a w s h 0)| ≤
      (gaussianDirectionalThirdConstant a/2)*‖w‖*‖h‖^3 := by
  have hh := segment_quadratic_remainder (fun t => gaussianDirectional a w (s+t • h))
    (gaussianDirectionalLineFirst a w s h) (gaussianDirectionalLineSecond a w s h)
    (gaussianDirectionalLineThird a w s h) (gaussianDirectionalThirdConstant a*‖w‖*‖h‖^3)
    (mul_nonneg (mul_nonneg (gaussianDirectionalThirdConstant_nonneg a ha) (norm_nonneg w))
      (by positivity)) (gaussianDirectional_line_deriv a w s h)
    (gaussianDirectional_first_deriv a w s h) (gaussianDirectional_second_deriv a w s h)
    (fun t _ => gaussianDirectional_third_bound a ha w s h t)
  have he : (gaussianDirectionalThirdConstant a*‖w‖*‖h‖^3)/2 =
      (gaussianDirectionalThirdConstant a/2)*‖w‖*‖h‖^3 := by ring
  simpa only [zero_smul, one_smul, add_zero, he] using hh

#print axioms gaussianDirectional_third_bound
#print axioms gaussianDirectional_quadratic_remainder
end SpectralRadiusUpperTail
