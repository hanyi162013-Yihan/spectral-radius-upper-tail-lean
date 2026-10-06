import SpectralRadiusUpperTail.RealSchurGapLawExplicitDensity
import SpectralRadiusUpperTail.GaussianErfcEnvelope
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

private theorem schur_gap_square_image (y : ℝ) (hy : 0 < y) :
    (fun t : ℝ => t^2-4*y^2) '' Ioi (2*y) = Ioi (0 : ℝ) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 2*y < t at ht
    have hsum : 0 < t+2*y := by linarith
    have hprod := mul_pos (sub_pos.mpr ht) hsum
    change 0 < t^2-4*y^2
    nlinarith
  · intro hs
    change 0 < s at hs
    let t := Real.sqrt (s+4*y^2)
    have hsq : t^2 = s+4*y^2 := Real.sq_sqrt (by positivity)
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have ht : 2*y < t := by nlinarith [sq_pos_of_pos hy]
    refine ⟨t, ht, ?_⟩
    nlinarith

private theorem schur_gap_square_injOn (y : ℝ) (hy : 0 < y) :
    InjOn (fun t : ℝ => t^2-4*y^2) (Ioi (2*y)) := by
  intro a ha b hb hab
  change 2*y < a at ha
  change 2*y < b at hb
  change a^2-4*y^2 = b^2-4*y^2 at hab
  have ha0 : 0 < a := by linarith [ha]
  have hb0 : 0 < b := by linarith [hb]
  have hsq : a^2 = b^2 := by nlinarith [hab]
  nlinarith

private theorem schur_gap_square_deriv (y t : ℝ) :
    HasDerivAt (fun z : ℝ => z^2-4*y^2) (2*t) t := by
  convert (hasDerivAt_pow 2 t).sub_const (4*y^2) using 1 <;> try rfl
  all_goals norm_num

/-- The inverse-square-root gap integral is an ordinary Gaussian upper
tail after the substitution `s=t²-4y²`. This is the first exact step toward
the erfc normalizer, independent of any matrix distribution. -/
theorem schur_gap_integral_eq_gaussian_tail (n y : ℝ)
    (hy : 0 < y) :
    (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) =
      2*Real.exp (2*n*y^2) *
        (∫ t : ℝ in Ioi (2*y),
          Real.exp (-(n/2)*t^2)) := by
  let f : ℝ → ℝ := fun t => t^2-4*y^2
  let g : ℝ → ℝ := fun s =>
    Real.exp (-(n/2)*s) * (Real.sqrt (s+4*y^2))⁻¹
  have hder : ∀ t ∈ Ioi (2*y),
      HasDerivWithinAt f (2*t) (Ioi (2*y)) t := by
    intro t ht
    exact (schur_gap_square_deriv y t).hasDerivWithinAt
  have hcov := integral_image_eq_integral_abs_deriv_smul
    (f := f) (f' := fun t => 2*t)
    (s := Ioi (2*y)) measurableSet_Ioi hder
    (schur_gap_square_injOn y hy) g
  rw [schur_gap_square_image y hy] at hcov
  have hpoint : ∀ t ∈ Ioi (2*y),
      |2*t| * g (f t) =
        2*Real.exp (2*n*y^2)*Real.exp (-(n/2)*t^2) := by
    intro t ht
    change 2*y < t at ht
    have htpos : 0 < t := by linarith [ht]
    have hroot : Real.sqrt ((t^2-4*y^2)+4*y^2) = t := by
      have he : (t^2-4*y^2)+4*y^2 = t^2 := by ring
      rw [he, Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    have hexp : Real.exp (-(n/2)*(t^2-4*y^2)) =
        Real.exp (2*n*y^2)*Real.exp (-(n/2)*t^2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [f,g]
    rw [abs_of_pos (by positivity : 0 < 2*t), hroot, hexp]
    field_simp
  calc
    (∫ s : ℝ in Ioi 0, g s) =
        ∫ t : ℝ in Ioi (2*y), |2*t| * g (f t) := by
      simpa only [smul_eq_mul] using hcov
    _ = ∫ t : ℝ in Ioi (2*y),
          2*Real.exp (2*n*y^2)*Real.exp (-(n/2)*t^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact hpoint
    _ = _ := by rw [integral_const_mul]

/-- Exact erfc evaluation of the local squared-gap normalizer, for a
positive imaginary part. -/
theorem schur_gap_integral_eq_erfc (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) =
      (Real.sqrt Real.pi / Real.sqrt (n/2)) *
        Real.exp (2*n*y^2) *
        gaussianErfc (2*Real.sqrt (n/2)*y) := by
  let a : ℝ := Real.sqrt (n/2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a^2 = n/2 := Real.sq_sqrt (by linarith)
  have htail := integral_comp_mul_left_Ioi
    (fun z : ℝ => Real.exp (-z^2)) (2*y) (b := a) ha
  have hfun : (fun t : ℝ => Real.exp (-(n/2)*t^2)) =
      (fun t : ℝ => Real.exp (-(a*t)^2)) := by
    funext t
    congr 1
    rw [mul_pow, ha2]
    ring
  have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  calc
    (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) =
      2*Real.exp (2*n*y^2) *
        (∫ t : ℝ in Ioi (2*y), Real.exp (-(n/2)*t^2)) :=
          schur_gap_integral_eq_gaussian_tail n y hy
    _ = 2*Real.exp (2*n*y^2) *
        (a⁻¹ * (∫ z : ℝ in Ioi (a*(2*y)), Real.exp (-z^2))) := by
      rw [hfun]
      simpa only [smul_eq_mul] using
        congrArg (fun v : ℝ => 2*Real.exp (2*n*y^2)*v) htail
    _ = (Real.sqrt Real.pi / a) * Real.exp (2*n*y^2) *
        gaussianErfc (a*(2*y)) := by
      unfold gaussianErfc
      field_simp
    _ = _ := by dsimp [a]; ring

/-- Same exact normalizer in the scaling convention used by the real
Ginibre nonreal one-point expression. -/
theorem schur_gap_integral_eq_scaled_erfc (n y : ℝ)
    (hn : 0 < n) (hy : 0 < y) :
    (∫ s : ℝ in Ioi 0,
      Real.exp (-(n/2)*s) *
        (Real.sqrt (s+4*y^2))⁻¹) =
      Real.sqrt (2*Real.pi/n) *
        Real.exp (2*n*y^2) *
        gaussianErfc (Real.sqrt (2*n)*y) := by
  have hn2 : 0 ≤ n/2 := by linarith
  have h2n : 0 ≤ 2*n := by positivity
  have harg : 2*Real.sqrt (n/2) = Real.sqrt (2*n) := by
    have hsq1 := Real.sq_sqrt hn2
    have hsq2 := Real.sq_sqrt h2n
    nlinarith [Real.sqrt_nonneg (n/2), Real.sqrt_nonneg (2*n)]
  have hpref : Real.sqrt Real.pi / Real.sqrt (n/2) =
      Real.sqrt (2*Real.pi/n) := by
    rw [← Real.sqrt_div Real.pi_nonneg]
    congr 1
    field_simp [hn.ne']
  rw [schur_gap_integral_eq_erfc n y hn hy, hpref, ← harg]

#print axioms schur_gap_integral_eq_gaussian_tail
#print axioms schur_gap_integral_eq_erfc
#print axioms schur_gap_integral_eq_scaled_erfc
end SpectralRadiusUpperTail
