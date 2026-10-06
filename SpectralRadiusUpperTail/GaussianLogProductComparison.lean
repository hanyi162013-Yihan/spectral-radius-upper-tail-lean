import SpectralRadiusUpperTail.GaussianLogNormalizerComparison
import SpectralRadiusUpperTail.FiniteLogProduct

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianNormalizerLogErrorConstant (μ ν : Measure 𝕂) (a K : ℝ) : ℝ :=
  ((gaussianThirdConstant a/2)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))/
    Real.exp (-(K^2+1)/a)

lemma gaussianNormalizer_product_log_comparison_flat (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hmμ : (∫ x : 𝕂, x ∂μ) = 0) (hmν : (∫ x : 𝕂, x ∂ν) = 0)
    (hvarμ : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (hvarν : (∫ x : 𝕂, ‖x‖^2 ∂ν) = 1)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂)
    (hv : ∑ i, ‖v i‖^2 ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ) (hflat : ∀ i, ‖v i‖ ≤ δ)
    (t : Fin N → 𝕂) (K : ℝ) (ht : ∀ i, ‖t i‖ ≤ K) :
    |Real.log (∏ i, gaussianFiniteNormalizer μ a v (t i))-
      Real.log (∏ i, gaussianFiniteNormalizer ν a v (t i))| ≤
      (N : ℝ)*gaussianNormalizerLogErrorConstant μ ν a K*δ := by
  have hposμ : ∀ i, 0 < gaussianFiniteNormalizer μ a v (t i) := fun i =>
    (Real.exp_pos _).trans_le
      (gaussianFiniteNormalizer_lower μ hXμ hmμ hvarμ a ha v hv (t i) K (ht i))
  have hposν : ∀ i, 0 < gaussianFiniteNormalizer ν a v (t i) := fun i =>
    (Real.exp_pos _).trans_le
      (gaussianFiniteNormalizer_lower ν hXν hmν hvarν a ha v hv (t i) K (ht i))
  have hrow : ∀ i, |Real.log (gaussianFiniteNormalizer μ a v (t i))-
      Real.log (gaussianFiniteNormalizer ν a v (t i))| ≤
        gaussianNormalizerLogErrorConstant μ ν a K*δ := by
    intro i
    have hh := gaussianFinite_log_comparison_flat μ ν hXμ hXν hmμ hmν hvarμ hvarν
      hpseudo h3μ h3ν a ha N v hv δ hδ hflat (t i) K (ht i)
    apply hh.trans_eq
    unfold gaussianNormalizerLogErrorConstant
    ring
  have hh := finite_log_product_difference_bound
    (fun i => gaussianFiniteNormalizer μ a v (t i))
    (fun i => gaussianFiniteNormalizer ν a v (t i)) hposμ hposν
    (gaussianNormalizerLogErrorConstant μ ν a K*δ) hrow
  simpa only [Fintype.card_fin,mul_assoc] using hh

#print axioms gaussianNormalizerLogErrorConstant
#print axioms gaussianNormalizer_product_log_comparison_flat
end SpectralRadiusUpperTail
