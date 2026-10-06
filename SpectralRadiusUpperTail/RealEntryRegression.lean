import SpectralRadiusUpperTail.GaussianEntryRegression
import SpectralRadiusUpperTail.RealGaussianFiniteScore
import SpectralRadiusUpperTail.ProjectionError

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Actual real conditional-entry mean regression from the original entry law.
The error separates the current-entry Taylor term and the future Gaussian replacement. -/
theorem real_gaussian_entry_regression (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℝ) (b s : ℝ)
    (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |(∫ x : ℝ, x ∂gaussianEntryLaw μ a v b s)-2*b*s/(a+2*∑ i, ‖v i‖^2)| ≤
      gaussianEntryTaylorConstant a K 1 (∫ x : ℝ, ‖x‖^3 ∂μ)*‖b‖^2+
      gaussianScoreComparisonConstant a K*‖b‖*
        ((∫ x : ℝ, ‖x‖^3 ∂μ)+(∫ x : ℝ, ‖x‖^3 ∂standardNormal))*(∑ i, ‖v i‖^3) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (squareExp_norm_pow_integrable μ τ hτ he 2)
  have h3 := squareExp_norm_pow_integrable μ τ hτ he 3
  have hv' : ∑ i, ‖v i‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  have hr := gaussianEntry_mean_score μ hX hm hvar h3 1 (real_unit_covariance μ hvar)
    a ha v b s 1 hv K hs
  simp only [Real.inner_apply, one_mul, mul_one, norm_one] at hr
  have hg := real_gaussian_linear_score_comparison μ hm hvar τ hτ he a ha N v hv' b s K hs
  have hh := linear_score_error_combine (∫ x : ℝ, x ∂gaussianEntryLaw μ a v b s) _ _ 1
    (gaussianEntryTaylorConstant a K 1 (∫ x : ℝ, ‖x‖^3 ∂μ)*‖b‖^2) _
    (by simpa only [one_mul] using hr) hg
  simp only [abs_one, one_mul] at hh
  convert! hh using 1 <;> congr 1 <;> ring

#print axioms real_gaussian_entry_regression
end SpectralRadiusUpperTail
