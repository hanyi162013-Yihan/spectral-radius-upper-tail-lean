import SpectralRadiusUpperTail.GaussianEntryRegression
import SpectralRadiusUpperTail.ComplexGaussianFiniteScore
import SpectralRadiusUpperTail.ProjectionError

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Actual proper-complex conditional-entry mean regression. The conjugate
coefficient and covariance factor are derived without independent entry components. -/
theorem complex_gaussian_entry_regression (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℂ) (b s : ℂ)
    (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) (K : ℝ) (hs : ‖s‖ ≤ K) :
    ‖(∫ x : ℂ, x ∂gaussianEntryLaw μ a v b s)-
      (1/(a+∑ i, ‖v i‖^2) : ℝ) • (star b*s)‖ ≤
      gaussianEntryTaylorConstant a K (1/2) (∫ x : ℂ, ‖x‖^3 ∂μ)*‖b‖^2+
      (1/2)*gaussianScoreComparisonConstant a K*‖b‖*
        ((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian))*(∑ i, ‖v i‖^3) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (squareExp_norm_pow_integrable μ τ hτ he 2)
  have h3 := squareExp_norm_pow_integrable μ τ hτ he 3
  have hv' : ∑ i, ‖v i‖^2 ≤ 1 := by nlinarith [sq_nonneg ‖b‖]
  have hm3 : 0 ≤ ∫ x : ℂ, ‖x‖^3 ∂μ := integral_nonneg (fun _ => by positivity)
  have hg3 : 0 ≤ ∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian := integral_nonneg (fun _ => by positivity)
  have ht : 0 ≤ gaussianEntryTaylorConstant a K (1/2) (∫ x : ℂ, ‖x‖^3 ∂μ) := by
    unfold gaussianEntryTaylorConstant
    positivity
  have hC : 0 ≤ gaussianScoreComparisonConstant a K := by
    unfold gaussianScoreComparisonConstant gaussianDirectionalThirdConstant gaussianThirdConstant
    positivity
  apply norm_le_of_projection_error _ _ (by positivity)
  intro w
  have hr := gaussianEntry_mean_score μ hX hm hvar h3 (1/2)
    (proper_unit_covariance μ hX hvar hpseudo) a ha v b s w hv K hs
  have hg := complex_gaussian_linear_score_comparison μ hm hvar hpseudo τ hτ he
    a ha N v hv' (b*w) s K hs
  have hh := linear_score_error_combine _ _ _ (1/2) _ _ hr hg
  rw [inner_sub_right, complex_projection_scaled_regression]
  calc
    _ = |inner ℝ w (∫ x : ℂ, x ∂gaussianEntryLaw μ a v b s)-
        (1/2)*(2*inner ℝ s (b*w)/(a+∑ i, ‖v i‖^2))| := by congr 1; ring
    _ ≤ _ := hh
    _ = _ := by rw [norm_mul]; norm_num; ring

#print axioms complex_gaussian_entry_regression
end SpectralRadiusUpperTail
