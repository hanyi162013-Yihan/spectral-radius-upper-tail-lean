import SpectralRadiusUpperTail.GaussianEntryKernel
import Mathlib.Analysis.Normed.Operator.Mul

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def gaussianEntryLinear (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (b s : 𝕂) : 𝕂 →L[ℝ] ℝ :=
  (gaussianConvolutionLinear (finiteRowSumLaw μ v) a s).comp (ContinuousLinearMap.mul ℝ 𝕂 b)

lemma gaussianEntryLinear_apply (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s w : 𝕂) :
    gaussianEntryLinear μ a v b s w = gaussianFiniteDirectional μ a v (b*w) s := by
  rw [gaussianFiniteDirectional_eq_linear μ a ha]
  rfl

lemma gaussianEntryLinear_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s w : 𝕂) :
    |gaussianEntryLinear μ a v b s w| ≤ ((2/a)*(1+a))*‖b‖*‖w‖ := by
  change |gaussianConvolutionLinear (finiteRowSumLaw μ v) a s (b*w)| ≤ _
  calc
    _ ≤ ‖gaussianConvolutionLinear (finiteRowSumLaw μ v) a s‖*‖b*w‖ := by
      simpa only [Real.norm_eq_abs] using
        (gaussianConvolutionLinear (finiteRowSumLaw μ v) a s).le_opNorm (b*w)
    _ ≤ ((2/a)*(1+a))*‖b*w‖ := mul_le_mul_of_nonneg_right
      (gaussianConvolutionLinear_norm_le _ a ha s) (norm_nonneg _)
    _ = _ := by rw [norm_mul]; ring

lemma gaussianEntry_linear_remainder (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s x : 𝕂) :
    |gaussianFiniteNormalizer μ a v (s-b*x)-
      (gaussianFiniteNormalizer μ a v s-gaussianEntryLinear μ a v b s x)| ≤
      ((6/a)*‖b‖^2)*‖x‖^2 := by
  have hh := gaussianConvolution_linear_remainder (finiteRowSumLaw μ v) a ha s (-(b*x))
  rw [map_neg] at hh
  simp only [norm_neg, norm_mul, mul_pow] at hh
  simpa only [gaussianFiniteNormalizer_eq_convolution, gaussianEntryLinear,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', sub_eq_add_neg,
    mul_assoc] using hh

/-- Actual entry/future integrals have a quadratic denominator error and a
third-moment numerator error, with the covariance normalization retained. -/
theorem gaussianEntry_taylor_bounds (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (h3 : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (c : ℝ) (hc : ∀ z : 𝕂, (∫ x : 𝕂, (inner ℝ z x)^2 ∂μ) = c*‖z‖^2)
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (b s w : 𝕂) :
    |gaussianEntryNormalizer μ a v b s-gaussianFiniteNormalizer μ a v s| ≤ (6/a)*‖b‖^2 ∧
    |(∫ x : 𝕂, inner ℝ w x*gaussianFiniteNormalizer μ a v (s-b*x) ∂μ)+
      c*gaussianEntryLinear μ a v b s w| ≤
        ((6/a)*‖b‖^2)*‖w‖*(∫ x : 𝕂, ‖x‖^3 ∂μ) := by
  have hf := gaussianEntry_weight_measurable μ hX a ha v b s
  have hb (x : 𝕂) : |gaussianFiniteNormalizer μ a v (s-b*x)| ≤ 1 := by
    rw [abs_of_nonneg (gaussianFiniteNormalizer_bounds μ a ha v _).1]
    exact (gaussianFiniteNormalizer_bounds μ a ha v _).2
  obtain ⟨hi, hwi⟩ := bounded_weight_projection_integrable μ hX _ hf hb w
  exact ⟨centered_linear_taylor_denominator μ hX hm hvar _ hi _ _ _
    (gaussianEntry_linear_remainder μ a ha v b s),
    isotropic_linear_taylor_numerator μ hX hm h3 c hc _ _ _ (by positivity) _ w hwi
      (gaussianEntry_linear_remainder μ a ha v b s)⟩

#print axioms gaussianEntry_linear_remainder
#print axioms gaussianEntry_taylor_bounds
end SpectralRadiusUpperTail
