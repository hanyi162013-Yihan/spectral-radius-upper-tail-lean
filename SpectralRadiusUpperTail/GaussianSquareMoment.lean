import SpectralRadiusUpperTail.GaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma standardNormal_quarter_density (x : ℝ) :
    gaussianPDFReal 0 1 x*Real.exp (x^2/4) ≤ 2*gaussianPDFReal 0 2 x := by
  have h1 : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (2*Real.pi*2) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (2*Real.pi*2) ≤ 2*Real.sqrt (2*Real.pi) := by
    have hs1 := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hs2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi*2 by positivity)
    nlinarith
  have hc : (Real.sqrt (2*Real.pi))⁻¹ ≤ 2*(Real.sqrt (2*Real.pi*2))⁻¹ := by
    have h := (div_le_div_iff₀ h1 h2).mpr (show 1*Real.sqrt (2*Real.pi*2) ≤
      2*Real.sqrt (2*Real.pi) by simpa using hs)
    simpa only [one_div, div_eq_mul_inv, one_mul] using h
  have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-x^2/4))
  have he1 : gaussianPDFReal 0 1 x*Real.exp (x^2/4) =
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/4) := by
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have he2 : gaussianPDFReal 0 2 x =
      (Real.sqrt (2*Real.pi*2))⁻¹*Real.exp (-x^2/4) := by
    norm_num [gaussianPDFReal]
  rw [he1, he2]
  nlinarith only [hh]

/-- A concrete finite Gaussian exponential-square moment used for Gaussian
linearization; no prior integrability of the variable to be linearized is needed. -/
theorem standardNormal_exp_quarter_sq :
    Integrable (fun x : ℝ => Real.exp (x^2/4)) standardNormal ∧
      (∫ x : ℝ, Real.exp (x^2/4) ∂standardNormal) ≤ 2 := by
  have hden : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x*Real.exp (x^2/4)) volume := by
    apply ((integrable_gaussianPDFReal 0 2).const_mul 2).mono_nonneg (by fun_prop)
    · exact Filter.Eventually.of_forall (fun x => mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (Real.exp_nonneg _))
    · exact Filter.Eventually.of_forall standardNormal_quarter_density
  have hi : Integrable (fun x : ℝ => Real.exp (x^2/4)) standardNormal := by
    rw [standardNormal, gaussianReal_of_var_ne_zero _ (by norm_num),
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hden
  refine ⟨hi, ?_⟩
  have hh := integral_mono hden ((integrable_gaussianPDFReal 0 2).const_mul 2)
    standardNormal_quarter_density
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 (by norm_num), mul_one] at hh
  change (∫ x : ℝ, Real.exp (x^2/4) ∂gaussianReal 0 1) ≤ 2
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul] using hh

#print axioms standardNormal_exp_quarter_sq
end SpectralRadiusUpperTail
