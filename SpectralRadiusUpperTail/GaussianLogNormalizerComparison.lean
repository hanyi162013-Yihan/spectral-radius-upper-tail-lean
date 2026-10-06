import SpectralRadiusUpperTail.GaussianScoreComparison
import SpectralRadiusUpperTail.LogPositiveStability

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma gaussianFinite_log_comparison_flat (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hmμ : (∫ x : 𝕂, x ∂μ) = 0) (hmν : (∫ x : 𝕂, x ∂ν) = 0)
    (hvarμ : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (hvarν : (∫ x : 𝕂, ‖x‖^2 ∂ν) = 1)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂)
    (hv : ∑ i, ‖v i‖^2 ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) (hflat : ∀ i, ‖v i‖ ≤ δ)
    (s : 𝕂) (K : ℝ) (hs : ‖s‖ ≤ K) :
    |Real.log (gaussianFiniteNormalizer μ a v s)-Real.log (gaussianFiniteNormalizer ν a v s)| ≤
      (((gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*δ)/
        Real.exp (-(K^2+1)/a) := by
  have hl := abs_log_sub_log_le_of_lower (gaussianFiniteNormalizer μ a v s)
    (gaussianFiniteNormalizer ν a v s) (Real.exp (-(K^2+1)/a)) (Real.exp_pos _)
    (gaussianFiniteNormalizer_lower μ hXμ hmμ hvarμ a ha v hv s K hs)
    (gaussianFiniteNormalizer_lower ν hXν hmν hvarν a ha v hv s K hs)
  have hr := gaussian_product_replacement_flat μ ν hXμ hXν (hmμ.trans hmν.symm)
    (hvarμ.trans hvarν.symm) hpseudo h3μ h3ν a ha N v s δ hδ hflat hv
  exact hl.trans (div_le_div_of_nonneg_right hr (Real.exp_pos _).le)

#print axioms gaussianFinite_log_comparison_flat
end SpectralRadiusUpperTail
