import SpectralRadiusUpperTail.GaussianGlobalMean
import SpectralRadiusUpperTail.GlobalRegressionEnvelope

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual real or complex conditional regression remainder has a global
integrable-envelope shape, uniformly over the length and coefficients of the future. -/
theorem gaussianEntry_regression_global_square (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (d : ℝ) (hd : 0 < d) (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (b s : 𝕂)
    (hv : ‖b‖^2+∑ i : Fin N, ‖v i.val‖^2 ≤ 1)
    (hsmall : gaussianGlobalScoreConstant μ a d*‖b‖^2 ≤ d)
    (t : ℝ) (ht : 0 < t) :
    ‖(∫ x : 𝕂, x ∂gaussianEntryLaw μ a (fun i : Fin N => v i.val) b s)-
      (1/(t+(∑ i : Fin N, ‖v i.val‖^2)+‖b‖^2) : ℝ) • (star b*s)‖^2 ≤
      (4*((gaussianGlobalMeanConstant μ a d)^2+1/t^2))*‖b‖^2*(1+‖s‖^2)*
        Real.exp ((4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖b‖^2*(1+‖s‖^2)) := by
  have hC : 0 ≤ gaussianGlobalScoreConstant μ a d := by
    unfold gaussianGlobalScoreConstant gaussianScoreConstant
    positivity
  have hM : 0 ≤ ∫ x : 𝕂, (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2) ∂μ :=
    integral_nonneg (fun x => by positivity)
  have hA : 0 ≤ gaussianGlobalMeanConstant μ a d := by
    unfold gaussianGlobalMeanConstant
    exact mul_nonneg (mul_nonneg hC hM) (Real.exp_nonneg _)
  have hq : 0 ≤ ∑ i : Fin N, ‖v i.val‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact global_regression_square_bound _ b s t _ _ _ ht
    (by nlinarith [sq_nonneg ‖b‖]) hA (by positivity)
    (gaussianEntry_mean_global μ hm hvar d hd hexp v N a ha b s hv hsmall)

#print axioms gaussianEntry_regression_global_square
end SpectralRadiusUpperTail
