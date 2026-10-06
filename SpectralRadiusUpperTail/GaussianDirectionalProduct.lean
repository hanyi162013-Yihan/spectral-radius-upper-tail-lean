import SpectralRadiusUpperTail.ScalarGaussianDirectionalReplacement
import SpectralRadiusUpperTail.GaussianProductReplacement

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Actual finite-product replacement for the first directional Gaussian test,
with the same cubic coefficient sum as for the normalizer itself. -/
theorem gaussianDirectional_product_replacement (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hm : (∫ x : 𝕂, x ∂μ) = ∫ x : 𝕂, x ∂ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂) (w s : 𝕂) :
    |(∫ x : Fin N → 𝕂, gaussianDirectional a w (s-∑ i, v i*x i) ∂Measure.pi (fun _ => μ))-
      (∫ x : Fin N → 𝕂, gaussianDirectional a w (s-∑ i, v i*x i) ∂Measure.pi (fun _ => ν))| ≤
      (((gaussianDirectionalThirdConstant a/2)*‖w‖)*
        ((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*∑ i, ‖v i‖^3 := by
  let f := gaussianDirectional a w
  let C := ((gaussianDirectionalThirdConstant a/2)*‖w‖)*
    ((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν))
  have hf : Measurable f := by unfold f gaussianDirectional; fun_prop
  have hB (z : 𝕂) : |f z| ≤ (2/a)*(1+a)*‖w‖ := gaussianDirectional_bound a ha w z
  have hrep (i : Fin N) (t : 𝕂) :
      |(∫ x : 𝕂, f (t+(-v i)*x) ∂μ)-(∫ x : 𝕂, f (t+(-v i)*x) ∂ν)| ≤ C*‖v i‖^3 := by
    simpa only [f, C, norm_neg] using rclike_gaussianDirectional_scalar_replacement μ ν hXμ hXν
      hm hvar hpseudo h3μ h3ν a ha w t (-v i)
  have hh := bounded_product_sum_replacement f hf ((2/a)*(1+a)*‖w‖) hB N
    (fun _ => μ) (fun _ => ν) (fun i x => (-v i)*x) (fun _ => by fun_prop)
    (fun i => C*‖v i‖^3) hrep s
  simpa only [f, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.mul_sum] using hh

lemma gaussianDirectional_product_replacement_flat (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hm : (∫ x : 𝕂, x ∂μ) = ∫ x : 𝕂, x ∂ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → 𝕂) (w s : 𝕂) (ε : ℝ)
    (hε : 0 ≤ ε) (hmax : ∀ i, ‖v i‖ ≤ ε) (henergy : ∑ i, ‖v i‖^2 ≤ 1) :
    |(∫ x : Fin N → 𝕂, gaussianDirectional a w (s-∑ i, v i*x i) ∂Measure.pi (fun _ => μ))-
      (∫ x : Fin N → 𝕂, gaussianDirectional a w (s-∑ i, v i*x i) ∂Measure.pi (fun _ => ν))| ≤
      (((gaussianDirectionalThirdConstant a/2)*‖w‖)*
        ((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*ε := by
  apply (gaussianDirectional_product_replacement μ ν hXμ hXν hm hvar hpseudo h3μ h3ν a ha N v w s).trans
  apply mul_le_mul_of_nonneg_left (coefficient_cube_sum_le v ε hε hmax henergy)
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (gaussianDirectionalThirdConstant_nonneg a ha) (by norm_num))
      (norm_nonneg w)
  · exact add_nonneg (integral_nonneg (fun x => by positivity)) (integral_nonneg (fun x => by positivity))

#print axioms gaussianDirectional_product_replacement
#print axioms gaussianDirectional_product_replacement_flat
end SpectralRadiusUpperTail
