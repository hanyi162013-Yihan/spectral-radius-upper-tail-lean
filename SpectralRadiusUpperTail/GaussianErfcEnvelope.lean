import SpectralRadiusUpperTail.RightTailIntegralComparison
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- Complementary Gaussian error function, defined directly by its tail
integral so that no special-function library input is needed. -/
noncomputable def gaussianErfc (t : ℝ) : ℝ :=
  (2/Real.sqrt Real.pi) *
    (∫ x : ℝ in Ioi t, Real.exp (-x^2))

/-- The elementary Mills-ratio bound used in the nonreal real-Ginibre
one-point density. -/
theorem gaussian_tail_integral_upper (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ in Ioi t, Real.exp (-x^2)) ≤
      Real.exp (-t^2)/(2*t) := by
  have hf : IntegrableOn (fun x : ℝ => Real.exp (-x^2)) (Ioi t) := by
    have h := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)
    simpa using (h.integrableOn (s := Ioi t))
  apply right_tail_integral_le_of_exp_envelope
    (fun x : ℝ => Real.exp (-x^2)) t (Real.exp (-t^2)) (2*t)
    (by positivity) hf
  intro x hx
  have hs := sq_nonneg (x-t)
  have harg : -x^2 ≤ -t^2-(2*t)*(x-t) := by nlinarith
  calc
    Real.exp (-x^2) ≤ Real.exp (-t^2-(2*t)*(x-t)) := Real.exp_le_exp.mpr harg
    _ = Real.exp (-t^2)*Real.exp (-(2*t)*(x-t)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem gaussianErfc_upper (t : ℝ) (ht : 0 < t) :
    gaussianErfc t ≤ Real.exp (-t^2)/(Real.sqrt Real.pi*t) := by
  have hroot : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have htail := gaussian_tail_integral_upper t ht
  have hmul := mul_le_mul_of_nonneg_left htail
    (by positivity : 0 ≤ 2/Real.sqrt Real.pi)
  unfold gaussianErfc
  calc
    _ ≤ (2/Real.sqrt Real.pi)*(Real.exp (-t^2)/(2*t)) := hmul
    _ = Real.exp (-t^2)/(Real.sqrt Real.pi*t) := by
      field_simp

#print axioms gaussian_tail_integral_upper
#print axioms gaussianErfc_upper
end SpectralRadiusUpperTail
