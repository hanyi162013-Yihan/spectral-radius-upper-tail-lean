import SpectralRadiusUpperTail.GaussianLinearTaylor
import SpectralRadiusUpperTail.GaussianDirectionalIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma gaussianKernelDerivative_uniform_bound (a : ℝ) (ha : 0 < a) (s x : E) :
    ‖gaussianKernelDerivative a s x‖ ≤ (2/a)*(1+a) := by
  have hcoef : |(-2/a : ℝ)| = 2/a := by norm_num [abs_div, abs_of_pos ha]
  have hh := (gaussian_radial_odd_bounds a ‖s-x‖ ha).1
  simp only [gaussianKernelDerivative, norm_smul, Real.norm_eq_abs, hcoef,
    gaussianKernelReal, abs_of_nonneg (Real.exp_nonneg _), innerSL_apply_norm]
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 2/a)]

lemma gaussianKernelReal_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s : E) : Integrable (gaussianKernelReal a s) μ := by
  exact soft_exponential_integrable μ _ (by fun_prop) (fun _ => sq_nonneg _) a ha

lemma gaussianKernelDerivative_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s : E) : Integrable (gaussianKernelDerivative a s) μ := by
  apply (integrable_const ((2/a)*(1+a))).mono'
    (gaussianKernelDerivative_continuous a s).aestronglyMeasurable
  exact Filter.Eventually.of_forall (gaussianKernelDerivative_uniform_bound a ha s)

noncomputable def gaussianConvolutionLinear (μ : Measure E) (a : ℝ) (s : E) : E →L[ℝ] ℝ :=
  ∫ x, gaussianKernelDerivative a s x ∂μ

lemma gaussianConvolutionLinear_apply (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s h : E) :
    gaussianConvolutionLinear μ a s h = ∫ x, gaussianDirectional a h (s-x) ∂μ := by
  rw [gaussianConvolutionLinear,
    ContinuousLinearMap.integral_apply (gaussianKernelDerivative_integrable μ a ha s)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [gaussianKernelDerivative, gaussianKernelReal, smul_apply,
    innerSL_apply_apply, smul_eq_mul, gaussianDirectional]
  ring

lemma gaussianConvolutionLinear_norm_le (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s : E) :
    ‖gaussianConvolutionLinear μ a s‖ ≤ (2/a)*(1+a) := by
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (gaussianKernelDerivative_uniform_bound a ha s))
  simpa only [gaussianConvolutionLinear, probReal_univ, mul_one] using hh

/-- The actual averaged Gaussian weight inherits a uniform first-order Taylor
remainder, with no future moments required. -/
theorem gaussianConvolution_linear_remainder (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s h : E) :
    |gaussianConvolution μ a (s+h)-
      (gaussianConvolution μ a s+gaussianConvolutionLinear μ a s h)| ≤ (6/a)*‖h‖^2 := by
  have hi := gaussianKernelReal_integrable μ a ha s
  have hDi := gaussianKernelDerivative_integrable μ a ha s
  have hh := integral_difference_of_pointwise μ (gaussianKernelReal a (s+h))
    (fun x => gaussianKernelReal a s x+gaussianKernelDerivative a s x h)
    (gaussianKernelReal_integrable μ a ha (s+h)) (hi.add (hDi.apply_continuousLinearMap h))
    ((6/a)*‖h‖^2) (fun x => by
      simpa [gaussianKernelReal, gaussianKernelDerivative, gaussianDirectional,
        sub_add_eq_add_sub, smul_eq_mul, inner_sub_left, mul_assoc, mul_comm, mul_left_comm]
        using gaussian_linear_remainder a ha (s-x) h)
  rw [integral_add hi (hDi.apply_continuousLinearMap h),
    ← ContinuousLinearMap.integral_apply hDi] at hh
  exact hh

#print axioms gaussianConvolutionLinear_apply
#print axioms gaussianConvolutionLinear_norm_le
#print axioms gaussianConvolution_linear_remainder
end SpectralRadiusUpperTail
