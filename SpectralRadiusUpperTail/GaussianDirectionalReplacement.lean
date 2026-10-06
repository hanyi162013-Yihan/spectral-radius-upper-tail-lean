import SpectralRadiusUpperTail.GaussianDirectionalPolynomial

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma gaussianDirectionalShift_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (w s : E) :
    Integrable (fun x => gaussianDirectional a w (s+x)) μ := by
  apply (integrable_const ((2/a)*(1+a)*‖w‖)).mono'
    (by unfold gaussianDirectional; fun_prop)
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using gaussianDirectional_bound a ha w (s+x))

lemma gaussianDirectional_integral_polynomial_error (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (h3 : Integrable (fun x : E => ‖x‖^3) μ)
    (a : ℝ) (ha : 0 < a) (w s : E) :
    |(∫ x : E, gaussianDirectional a w (s+x) ∂μ)-
      (∫ x, gaussianDirectionalPolynomial a w s x ∂μ)| ≤
        ((gaussianDirectionalThirdConstant a/2)*‖w‖)*(∫ x : E, ‖x‖^3 ∂μ) := by
  rw [← integral_sub (gaussianDirectionalShift_integrable μ a ha w s)
    (gaussianDirectionalPolynomial_integral μ hX a w s).1]
  have hh := norm_integral_le_of_norm_le
    (f := fun x : E => gaussianDirectional a w (s+x)-gaussianDirectionalPolynomial a w s x)
    (h3.const_mul ((gaussianDirectionalThirdConstant a/2)*‖w‖))
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using gaussianDirectionalPolynomial_remainder a ha w s x))
  simpa only [Real.norm_eq_abs, integral_const_mul] using hh

/-- Actual one-law replacement for the first directional derivative of a
Gaussian soft test, using the proved mixed fourth derivative and moment cancellation. -/
theorem gaussianDirectional_integral_replacement (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : E => x) 2 μ) (hXν : MemLp (fun x : E => x) 2 ν)
    (hm : (∫ x : E, x ∂μ) = ∫ x : E, x ∂ν)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) = ∫ x : E, ‖x‖^2 ∂ν)
    (hcov : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = ∫ x : E, (inner ℝ s x)^2 ∂ν)
    (h3μ : Integrable (fun x : E => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : E => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (w s : E) :
    |(∫ x : E, gaussianDirectional a w (s+x) ∂μ)-
      (∫ x : E, gaussianDirectional a w (s+x) ∂ν)| ≤
      ((gaussianDirectionalThirdConstant a/2)*‖w‖)*
        ((∫ x : E, ‖x‖^3 ∂μ)+(∫ x : E, ‖x‖^3 ∂ν)) := by
  have hPeq := gaussianDirectionalPolynomial_integral_matching μ ν hXμ hXν hm hvar hcov a w s
  have hμ := gaussianDirectional_integral_polynomial_error μ hXμ h3μ a ha w s
  have hν := gaussianDirectional_integral_polynomial_error ν hXν h3ν a ha w s
  have ht := abs_sub_le (∫ x : E, gaussianDirectional a w (s+x) ∂μ)
    (∫ x, gaussianDirectionalPolynomial a w s x ∂μ)
    (∫ x : E, gaussianDirectional a w (s+x) ∂ν)
  rw [hPeq, abs_sub_comm (∫ x, gaussianDirectionalPolynomial a w s x ∂ν)] at ht
  rw [hPeq] at hμ
  nlinarith only [ht, hμ, hν]

#print axioms gaussianDirectional_integral_replacement
end SpectralRadiusUpperTail
