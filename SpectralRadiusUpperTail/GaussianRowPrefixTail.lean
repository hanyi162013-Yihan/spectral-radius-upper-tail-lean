import SpectralRadiusUpperTail.GaussianRowPrefixMoment
import SpectralRadiusUpperTail.RegressionEnvelopeTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

/-- The actual tilted row's weighted-prefix tails control exactly the weight
appearing in the global squared regression envelope. -/
theorem gaussianFiniteRowLaw_regression_weight_tail (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ)
    (v w : Fin N → 𝕂) (hv : ∑ i, ‖v i‖^2 ≤ 1) (hw : ∑ i, ‖w i‖^2 ≤ 1)
    (a : ℝ) (ha : 0 < a) (t : 𝕂) (K : ℝ) (ht : ‖t‖ ≤ K)
    (γ R : ℝ) (hR : 0 ≤ R)
    (hγ : γ ≤ (rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ))/8) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    let X := fun x : Fin N → 𝕂 => t-∑ i, w i*x i
    Integrable (fun x => (1+‖X x‖^2)*Real.exp (γ*(1+‖X x‖^2))) (gaussianFiniteRowLaw μ a v t) ∧
      (∫ x in {x | R < ‖X x‖}, (1+‖X x‖^2)*Real.exp (γ*(1+‖X x‖^2))
        ∂gaussianFiniteRowLaw μ a v t) ≤
      (Real.exp γ*(1+8/c))*Real.exp (-(c/4)*R^2)*
        (2*Real.exp ((K^2+1)/a+c*K^2)) := by
  let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
  let X := fun x : Fin N → 𝕂 => t-∑ i, w i*x i
  have hX : Measurable X := measurable_const.sub (Finset.measurable_sum _
    (fun i _ => measurable_const.mul (measurable_pi_apply i)))
  obtain ⟨hc, hi, hb⟩ := gaussianFiniteRowLaw_shifted_sum_squareExp μ hm hvar τ hτ hexp v w hv hw a ha t K ht
  have hγ' : γ ≤ (c/2)/4 := by convert! hγ using 1 <;> dsimp [c] <;> ring
  have hh := regression_envelope_tail (gaussianFiniteRowLaw μ a v t) X hX (c/2) γ
    (2*Real.exp ((K^2+1)/a+c*K^2)) R (by dsimp [c]; positivity) hγ' hR hi hb
  have heq : 4/(c/2) = 8/c := by ring
  have heq' : (c/2)/2 = c/4 := by ring
  rw [heq, heq'] at hh
  exact hh

#print axioms gaussianFiniteRowLaw_regression_weight_tail
end SpectralRadiusUpperTail
