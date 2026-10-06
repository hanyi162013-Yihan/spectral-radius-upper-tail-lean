import SpectralRadiusUpperTail.GaussianDirectionalProduct
import SpectralRadiusUpperTail.GaussianFiniteCalculus
import SpectralRadiusUpperTail.RatioStability

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianScoreComparisonConstant (a K : ℝ) : ℝ :=
  (gaussianDirectionalThirdConstant a/2)/Real.exp (-(K^2+1)/a)+
    ((2/a)*(1+a))*(gaussianThirdConstant a/2)/(Real.exp (-(K^2+1)/a))^2

/-- The actual directional logarithmic derivatives of two finite-product
Gaussian-soft normalizers differ by a uniform compact cubic-coefficient bound.
Both denominator lower bounds and differentiation under the integral are proved. -/
theorem gaussianFinite_score_comparison (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hmμ : (∫ x : 𝕂, x ∂μ) = 0) (hmν : (∫ x : 𝕂, x ∂ν) = 0)
    (hvarμ : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (hvarν : (∫ x : 𝕂, ‖x‖^2 ∂ν) = 1)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 ≤ 1)
    (w s : 𝕂) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer μ a v (s+t • w))) 0-
      deriv (fun t : ℝ => Real.log (gaussianFiniteNormalizer ν a v (s+t • w))) 0| ≤
      gaussianScoreComparisonConstant a K*‖w‖*
        ((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν))*(∑ i, ‖v i‖^3) := by
  rw [gaussianFiniteNormalizer_log_deriv μ hXμ hmμ hvarμ a ha v hv s w,
    gaussianFiniteNormalizer_log_deriv ν hXν hmν hvarν a ha v hv s w]
  have hm := hmμ.trans hmν.symm
  have hvv := hvarμ.trans hvarν.symm
  have hden := gaussian_product_replacement μ ν hXμ hXν hm hvv hpseudo h3μ h3ν a ha N v s
  have hnum := gaussianDirectional_product_replacement μ ν hXμ hXν hm hvv hpseudo h3μ h3ν a ha N v w s
  have hh := ratio_difference_bound (gaussianFiniteDirectional μ a v w s)
    (gaussianFiniteDirectional ν a v w s) (gaussianFiniteNormalizer μ a v s)
    (gaussianFiniteNormalizer ν a v s) (Real.exp (-(K^2+1)/a))
    (((gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*∑ i, ‖v i‖^3)
    ((((gaussianDirectionalThirdConstant a/2)*‖w‖)*
      ((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*∑ i, ‖v i‖^3)
    ((2/a)*(1+a)*‖w‖) (Real.exp_pos _)
    (gaussianFiniteNormalizer_lower μ hXμ hmμ hvarμ a ha v hv s K hs)
    (gaussianFiniteNormalizer_lower ν hXν hmν hvarν a ha v hv s K hs)
    hden hnum (gaussianFiniteDirectional_bound ν a ha v w s)
  apply hh.trans_eq
  unfold gaussianScoreComparisonConstant
  ring

#print axioms gaussianFinite_score_comparison
end SpectralRadiusUpperTail
