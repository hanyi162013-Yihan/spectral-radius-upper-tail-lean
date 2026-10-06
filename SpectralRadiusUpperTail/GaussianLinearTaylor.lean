import SpectralRadiusUpperTail.GaussianTaylorBound
import SpectralRadiusUpperTail.GaussianDirectionalBounds

namespace SpectralRadiusUpperTail

/-- First-order Taylor remainder on a unit segment, with a conservative constant. -/
theorem segment_linear_remainder (f f₁ f₂ : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h₀ : ∀ t, HasDerivAt f (f₁ t) t)
    (h₁ : ∀ t, HasDerivAt f₁ (f₂ t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f₂ t| ≤ C) :
    |f 1-(f 0+f₁ 0)| ≤ C := by
  let Q := fun t => f t+(1-t)*f₁ t
  have hQ (t : ℝ) : HasDerivAt Q ((1-t)*f₂ t) t := by
    have hh := (h₀ t).add (((hasDerivAt_id t).const_sub 1).mul (h₁ t))
    convert! hh using 1 <;> (try dsimp only [id_eq]) <;> ring
  have hQb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖(1-t)*f₂ t‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1-t)]
    calc
      _ ≤ (1-t)*C := mul_le_mul_of_nonneg_left (hb t ⟨ht.1, ht.2.le⟩) (by linarith [ht.2])
      _ ≤ C := by nlinarith [ht.1]
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hQ t).hasDerivWithinAt) hQb
  simpa [Q, Real.norm_eq_abs] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gaussianLine_second_bound (a : ℝ) (ha : 0 < a) (s h : E) (t : ℝ) :
    |gaussianLineSecond a s h t| ≤ (6/a)*‖h‖^2 := by
  let q := 2/a
  let r := ‖s+t • h‖
  let p := gaussianLineSlope a s h t
  let g := gaussianLine a s h t
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hg : 0 ≤ g := Real.exp_nonneg _
  have hcoef : |(-2/a : ℝ)| = q := by
    dsimp [q]
    rw [abs_div, abs_of_pos ha]
    norm_num
  have hp : |p| ≤ q*r*‖h‖ := by
    dsimp [p, gaussianLineSlope]
    rw [abs_mul, hcoef]
    calc
      _ ≤ q*(‖s+t • h‖*‖h‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hq
      _ = _ := by ring
  have hb : |(-2/a)*‖h‖^2+p^2| ≤ q*‖h‖^2+|p|^2 := by
    convert! abs_add_le ((-2/a)*‖h‖^2) (p^2) using 1 <;>
      simp only [abs_mul, abs_pow, hcoef, abs_of_nonneg (norm_nonneg h)]
  have h0 : g ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  have h2 : r^2*g ≤ a := by
    simpa [g, gaussianLine, r] using gaussian_radial_even_bound a r ha 1
  change |((-2/a)*‖h‖^2+p^2)*g| ≤ _
  rw [abs_mul, abs_of_nonneg hg]
  calc
    _ ≤ (q*‖h‖^2+|p|^2)*g := mul_le_mul_of_nonneg_right hb hg
    _ ≤ (q*‖h‖^2+(q*r*‖h‖)^2)*g := by gcongr
    _ = ‖h‖^2*(q*g+q^2*(r^2*g)) := by ring
    _ ≤ ‖h‖^2*(q+q^2*a) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hh0 := mul_le_mul_of_nonneg_left h0 hq
      have hh2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
      linarith
    _ = _ := by dsimp [q]; field_simp <;> ring

/-- Uniform first-order expansion of the actual Gaussian weight. -/
theorem gaussian_linear_remainder (a : ℝ) (ha : 0 < a) (s h : E) :
    |Real.exp (-‖s+h‖^2/a)-(Real.exp (-‖s‖^2/a)+gaussianDirectional a h s)| ≤
      (6/a)*‖h‖^2 := by
  have hh := segment_linear_remainder (gaussianLine a s h) (gaussianLineFirst a s h)
    (gaussianLineSecond a s h) ((6/a)*‖h‖^2) (by positivity)
    (gaussianLine_deriv a s h) (gaussianLine_first_deriv a s h)
    (fun t _ => gaussianLine_second_bound a ha s h t)
  simpa only [gaussianLine, gaussianLineFirst, gaussianLineSlope, gaussianDirectional,
    zero_smul, one_smul, add_zero] using hh

#print axioms segment_linear_remainder
#print axioms gaussianLine_second_bound
#print axioms gaussian_linear_remainder
end SpectralRadiusUpperTail
