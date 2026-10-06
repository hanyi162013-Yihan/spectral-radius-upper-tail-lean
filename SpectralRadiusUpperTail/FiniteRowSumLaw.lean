import SpectralRadiusUpperTail.GaussianFiniteCalculus
import SpectralRadiusUpperTail.GaussianConvolutionTaylor

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {N : ℕ}

noncomputable def finiteRowSumLaw (μ : Measure 𝕂) (v : Fin N → 𝕂) : Measure 𝕂 :=
  (Measure.pi (fun _ : Fin N => μ)).map (fun x => ∑ i, v i*x i)

instance finiteRowSumLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ] (v : Fin N → 𝕂) :
    IsProbabilityMeasure (finiteRowSumLaw μ v) :=
  Measure.isProbabilityMeasure_map (measurable_finite_sum _ (fun _ => by fun_prop)).aemeasurable

lemma finiteRowSumLaw_memLp (μ : Measure 𝕂) [IsProbabilityMeasure μ] (v : Fin N → 𝕂)
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) :
    MemLp (fun x : 𝕂 => x) 2 (finiteRowSumLaw μ v) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (measurable_finite_sum _ (fun _ => by fun_prop)).aemeasurable).mpr
  exact iid_linear_row_memLp μ v hX

lemma gaussianFiniteNormalizer_eq_convolution (μ : Measure 𝕂) (a : ℝ)
    (v : Fin N → 𝕂) (s : 𝕂) :
    gaussianFiniteNormalizer μ a v s = gaussianConvolution (finiteRowSumLaw μ v) a s := by
  rw [gaussianConvolution, finiteRowSumLaw, integral_map
    (measurable_finite_sum _ (fun _ => by fun_prop)).aemeasurable
    (gaussianKernelReal_continuous a s).aestronglyMeasurable]
  rfl

lemma gaussianFiniteDirectional_eq_linear (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (s w : 𝕂) :
    gaussianFiniteDirectional μ a v w s = gaussianConvolutionLinear (finiteRowSumLaw μ v) a s w := by
  rw [gaussianConvolutionLinear_apply _ a ha, finiteRowSumLaw,
    integral_map (measurable_finite_sum _ (fun _ => by fun_prop)).aemeasurable
      (by unfold gaussianDirectional; fun_prop)]
  rfl

lemma gaussianFiniteNormalizer_continuous (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) :
    Continuous (gaussianFiniteNormalizer μ a v) := by
  have hi := (finiteRowSumLaw_memLp μ v hX).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he : gaussianFiniteNormalizer μ a v = gaussianConvolution (finiteRowSumLaw μ v) a := by
    funext s
    exact gaussianFiniteNormalizer_eq_convolution μ a v s
  rw [he]
  exact continuous_iff_continuousAt.mpr (fun s =>
    (gaussianConvolution_hasFDerivAt _ hi a ha s).continuousAt)

lemma gaussianFiniteNormalizer_bounds (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v : Fin N → 𝕂) (s : 𝕂) :
    0 ≤ gaussianFiniteNormalizer μ a v s ∧ gaussianFiniteNormalizer μ a v s ≤ 1 := by
  constructor
  · exact integral_nonneg (fun _ => Real.exp_nonneg _)
  · have hh := integral_mono (μ := Measure.pi (fun _ : Fin N => μ))
      (show Integrable (fun x : Fin N → 𝕂 => Real.exp (-‖s-∑ i, v i*x i‖^2/a))
        (Measure.pi (fun _ => μ)) from
        soft_exponential_integrable _ _ (by fun_prop) (fun _ => sq_nonneg _) a ha)
      (integrable_const (1 : ℝ))
      (fun _ => Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) ha.le))
    convert! hh using 1 <;>
      simp only [gaussianFiniteNormalizer, integral_const, probReal_univ, smul_eq_mul, one_mul]

#print axioms gaussianFiniteNormalizer_eq_convolution
#print axioms gaussianFiniteDirectional_eq_linear
#print axioms gaussianFiniteNormalizer_bounds
end SpectralRadiusUpperTail
