import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma gaussian_radial_primitive (c : ℝ) (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -(2*c)⁻¹*Real.exp (-c*y^2))
      (x*Real.exp (-c*x^2)) x := by
  convert! (((hasDerivAt_pow 2 x).const_mul (-c)).exp.const_mul (-(2*c)⁻¹)) using 1
  field [hc.ne']

lemma gaussian_radial_integral_Ioo (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    (∫ x in Set.Ioo 0 R, x*Real.exp (-c*x^2)) = (1-Real.exp (-c*R^2))/(2*c) := by
  have hi : IntervalIntegrable (fun x : ℝ => x*Real.exp (-c*x^2)) volume 0 R :=
    (show Continuous (fun x : ℝ => x*Real.exp (-c*x^2)) by fun_prop).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => gaussian_radial_primitive c hc x) hi
  rw [intervalIntegral.integral_of_le hR,integral_Ioc_eq_integral_Ioo] at he
  simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,Real.exp_zero,mul_one,
    sub_neg_eq_add] at he
  rw [he]
  ring

lemma gaussian_radial_integral_Ioi (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Set.Ioi 0, x*Real.exp (-c*x^2)) = (2*c)⁻¹ := by
  have ht : Tendsto (fun x : ℝ => -(2*c)⁻¹*Real.exp (-c*x^2)) atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))).const_mul (-(2*c)⁻¹)
    simpa using hh
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x _ => gaussian_radial_primitive c hc x)
    (integrable_mul_exp_neg_mul_sq hc).integrableOn ht
  simpa using he

#print axioms gaussian_radial_primitive
#print axioms gaussian_radial_integral_Ioo
#print axioms gaussian_radial_integral_Ioi
end SpectralRadiusUpperTail
