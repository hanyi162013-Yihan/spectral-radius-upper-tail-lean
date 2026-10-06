import SpectralRadiusUpperTail.UniformRowSquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual recursive future-weight logarithm has a dimension-independent
increment bound under the original entry hypotheses. No exponential-moment
hypothesis on the future law remains. -/
theorem gaussianFutureWeight_log_increment_uniform (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a τ : ℝ)
    (ha : 0 < a) (hτ : 0 < τ)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (τ*‖x‖^2)) μ) :
    let c := rowSquareExpExponent τ (∫ x : 𝕂, Real.exp (τ*‖x‖^2) ∂μ)
    ∀ s h : 𝕂,
      |Real.log (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N (s-h)).toReal -
        Real.log (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N s).toReal| ≤
          gaussianScoreConstant a c (Real.log 2)*‖h‖*(1+‖s‖+‖h‖) := by
  obtain ⟨hc, he, hM⟩ := iidRowSumLaw_squareExp μ v N
    (hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hm hv τ hτ hexp
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp only
  intro s h
  apply gaussianFutureWeight_log_increment μ v N hX hm hvar hv a _ (Real.log 2)
    ha hc hL he _ s h
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hM

#print axioms gaussianFutureWeight_log_increment_uniform
end SpectralRadiusUpperTail
