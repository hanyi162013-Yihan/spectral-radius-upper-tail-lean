import SpectralRadiusUpperTail.RealEntryRegression
import SpectralRadiusUpperTail.ComplexEntryRegression
import SpectralRadiusUpperTail.RegressionDenominator

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Real conditional regression with the full tail denominator, including the
current entry. The parameter t is the positive regularization variance. -/
theorem real_gaussian_entry_regression_full_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℝ => Real.exp (τ*‖x‖^2)) μ)
    (t : ℝ) (ht : 0 < t) (N : ℕ) (v : Fin N → ℝ) (b s : ℝ)
    (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) (K : ℝ) (hs : ‖s‖ ≤ K) :
    ‖(∫ x : ℝ, x ∂gaussianEntryLaw μ (2*t) v b s)-
      (1/(t+(∑ i, ‖v i‖^2)+‖b‖^2) : ℝ) • (star b*s)‖ ≤
      gaussianEntryTaylorConstant (2*t) K 1 (∫ x : ℝ, ‖x‖^3 ∂μ)*‖b‖^2+
      gaussianScoreComparisonConstant (2*t) K*‖b‖*
        ((∫ x : ℝ, ‖x‖^3 ∂μ)+(∫ x : ℝ, ‖x‖^3 ∂standardNormal))*(∑ i, ‖v i‖^3)+
      (‖s‖/t^2)*‖b‖^3 := by
  have hbase := real_gaussian_entry_regression μ hm hvar τ hτ he (2*t) (by positivity) N v b s hv K hs
  have hq : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hden : 0 < t+∑ i, ‖v i‖^2 := by positivity
  have hden2 : 0 < 2*t+2*∑ i, ‖v i‖^2 := by positivity
  have heq : 2*b*s/(2*t+2*∑ i, ‖v i‖^2) =
      (1/(t+∑ i, ‖v i‖^2) : ℝ) • (star b*s) := by
    change 2*b*s/(2*t+2*∑ i, ‖v i‖^2) = (1/(t+∑ i, ‖v i‖^2))*(b*s)
    field_simp
  rw [heq] at hbase
  exact regression_denominator_shift _ b s t (t+∑ i, ‖v i‖^2) _ ht
    (by linarith) (by simpa only [Real.norm_eq_abs] using hbase)

/-- Proper-complex conditional regression with the same full tail denominator. -/
theorem complex_gaussian_entry_regression_full_tail (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (t : ℝ) (ht : 0 < t) (N : ℕ) (v : Fin N → ℂ) (b s : ℂ)
    (hv : ‖b‖^2+∑ i, ‖v i‖^2 ≤ 1) (K : ℝ) (hs : ‖s‖ ≤ K) :
    ‖(∫ x : ℂ, x ∂gaussianEntryLaw μ t v b s)-
      (1/(t+(∑ i, ‖v i‖^2)+‖b‖^2) : ℝ) • (star b*s)‖ ≤
      gaussianEntryTaylorConstant t K (1/2) (∫ x : ℂ, ‖x‖^3 ∂μ)*‖b‖^2+
      (1/2)*gaussianScoreComparisonConstant t K*‖b‖*
        ((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian))*(∑ i, ‖v i‖^3)+
      (‖s‖/t^2)*‖b‖^3 := by
  have hbase := complex_gaussian_entry_regression μ hm hvar hpseudo τ hτ he t ht N v b s hv K hs
  have hq : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact regression_denominator_shift _ b s t (t+∑ i, ‖v i‖^2) _ ht (by linarith) hbase

#print axioms real_gaussian_entry_regression_full_tail
#print axioms complex_gaussian_entry_regression_full_tail
end SpectralRadiusUpperTail
