import SpectralRadiusUpperTail.ScalarPushforwardMoments
import SpectralRadiusUpperTail.SquareExpPolynomialMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

lemma stdGaussian_inner_product (s t : ℂ) :
    (∫ x : ℂ, inner ℝ s x * inner ℝ t x ∂stdGaussian ℂ) = inner ℝ s t := by
  have hh := covarianceBilin_apply (μ := stdGaussian ℂ) IsGaussian.memLp_two_id s t
  simp only [covarianceBilin_stdGaussian, id_eq, integral_id_stdGaussian, sub_zero] at hh
  convert! hh.symm using 1

lemma stdGaussian_complex_component_moments :
    (∫ x : ℂ, x.re^2 ∂stdGaussian ℂ) = 1 ∧
    (∫ x : ℂ, x.im^2 ∂stdGaussian ℂ) = 1 ∧
    (∫ x : ℂ, x.re*x.im ∂stdGaussian ℂ) = 0 := by
  have h1 := stdGaussian_inner_product 1 1
  have hI := stdGaussian_inner_product Complex.I Complex.I
  have hcross := stdGaussian_inner_product 1 Complex.I
  have hr (x : ℂ) : inner ℝ (1 : ℂ) x = x.re := by
    simp [real_inner_eq_re_inner ℂ]
  have hi (x : ℂ) : inner ℝ Complex.I x = x.im := by
    simp [real_inner_eq_re_inner ℂ]
  simp only [hr, hi, Complex.one_re, Complex.I_im, Complex.I_re, ← pow_two] at h1 hI hcross
  exact ⟨h1, hI, hcross⟩

lemma stdGaussian_complex_energy_pseudo :
    (∫ x : ℂ, ‖x‖^2 ∂stdGaussian ℂ) = 2 ∧
    (∫ x : ℂ, x^2 ∂stdGaussian ℂ) = 0 := by
  have hX : MemLp (fun x : ℂ => x) 2 (stdGaussian ℂ) := IsGaussian.memLp_two_id
  have hr : MemLp (fun x : ℂ => x.re) 2 (stdGaussian ℂ) := hX.re
  have hi : MemLp (fun x : ℂ => x.im) 2 (stdGaussian ℂ) := hX.im
  have hr2 : Integrable (fun x : ℂ => x.re^2) (stdGaussian ℂ) := by
    convert! hr.integrable_mul hr using 1
    ext x
    simp [pow_two]
  have hi2 : Integrable (fun x : ℂ => x.im^2) (stdGaussian ℂ) := by
    convert! hi.integrable_mul hi using 1
    ext x
    simp [pow_two]
  have hx2 : Integrable (fun x : ℂ => x^2) (stdGaussian ℂ) := by
    convert! hX.integrable_mul hX using 1
    ext x
    simp [pow_two]
  obtain ⟨hrm, him, hcross⟩ := stdGaussian_complex_component_moments
  constructor
  · simp_rw [RCLike.norm_sq_eq_def, RCLike.re_eq_complex_re, RCLike.im_eq_complex_im, ← pow_two]
    rw [integral_add hr2 hi2, hrm, him]
    norm_num
  · apply Complex.ext
    · rw [← RCLike.re_eq_complex_re, ← integral_re hx2]
      simp only [RCLike.re_eq_complex_re]
      have he (x : ℂ) : (x^2).re = x.re^2-x.im^2 := by simp [pow_two]
      simp_rw [he]
      rw [integral_sub hr2 hi2, hrm, him]
      norm_num
    · rw [← RCLike.im_eq_complex_im, ← integral_im hx2]
      simp only [RCLike.im_eq_complex_im]
      have he (x : ℂ) : (x^2).im = 2*(x.re*x.im) := by simp [pow_two]; ring
      simp_rw [he]
      rw [integral_const_mul, hcross]
      norm_num

/-- The actual proper complex Gaussian: a standard Gaussian on the real plane,
scaled to unit absolute second moment. -/
noncomputable def properComplexGaussian : Measure ℂ :=
  scalarPushforward (stdGaussian ℂ) ((Real.sqrt 2)⁻¹ : ℝ)

instance properComplexGaussian_probability : IsProbabilityMeasure properComplexGaussian :=
  scalarPushforward_probability _ _

lemma properComplexGaussian_memLp : MemLp (fun x : ℂ => x) 2 properComplexGaussian :=
  scalarPushforward_memLp _ _ IsGaussian.memLp_two_id

lemma properComplexGaussian_mean : (∫ x : ℂ, x ∂properComplexGaussian) = 0 := by
  rw [properComplexGaussian, scalarPushforward_mean, integral_id_stdGaussian, mul_zero]

lemma properComplexGaussian_energy : (∫ x : ℂ, ‖x‖^2 ∂properComplexGaussian) = 1 := by
  rw [properComplexGaussian, scalarPushforward_energy, stdGaussian_complex_energy_pseudo.1]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

lemma properComplexGaussian_pseudo : (∫ x : ℂ, x^2 ∂properComplexGaussian) = 0 := by
  rw [properComplexGaussian, scalarPushforward_pseudovariance,
    stdGaussian_complex_energy_pseudo.2, mul_zero]

lemma properComplexGaussian_third_integrable :
    Integrable (fun x : ℂ => ‖x‖^3) properComplexGaussian := by
  obtain ⟨c, hc, he⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian ℂ)
  exact (scalarPushforward_thirdMoment _ _
    (squareExp_norm_pow_integrable _ c hc he 3)).1

#print axioms properComplexGaussian_energy
#print axioms properComplexGaussian_pseudo
#print axioms properComplexGaussian_third_integrable
end SpectralRadiusUpperTail
