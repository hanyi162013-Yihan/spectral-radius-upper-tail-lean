import SpectralRadiusUpperTail.GaussianRowLaw
import SpectralRadiusUpperTail.GaussianDifferentiation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def iidRowSumLaw (μ : Measure 𝕂) (v : ℕ → 𝕂) (N : ℕ) : Measure 𝕂 :=
  (Measure.pi (fun _ : Fin N => μ)).map (fun s => ∑ i : Fin N, v i.val*s i)

lemma iidRowSum_measurable (v : ℕ → 𝕂) (N : ℕ) :
    Measurable (fun s : Fin N → 𝕂 => ∑ i : Fin N, v i.val*s i) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))

/-- The actual product-row normalizer is the Gaussian convolution of the
actual pushforward law of the row sum. -/
theorem gaussianRowNormalizer_eq_convolution (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    gaussianRowNormalizer μ v a N t =
      ENNReal.ofReal (gaussianConvolution (iidRowSumLaw μ v N) a t) := by
  let q := fun s : Fin N → 𝕂 => ‖t-∑ i : Fin N, v i.val*s i‖^2
  have hq : Measurable q :=
    (measurable_const.sub (iidRowSum_measurable v N)).norm.pow_const 2
  have hi := soft_exponential_integrable (Measure.pi (fun _ : Fin N => μ)) q hq
    (fun _ => sq_nonneg _) a ha
  rw [gaussianConvolution, iidRowSumLaw,
    integral_map (iidRowSum_measurable v N).aemeasurable
      (gaussianKernelReal_continuous a t).aestronglyMeasurable]
  change gaussianRowNormalizer μ v a N t =
    ENNReal.ofReal (∫ s, Real.exp (-q s/a) ∂Measure.pi (fun _ : Fin N => μ))
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))]
  rfl

/-- Recursive Gaussian future weights and Gaussian convolution use exactly the
same finite-sum probability law, not merely matching normalizing constants. -/
theorem gaussianFutureWeight_eq_convolution (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t =
      ENNReal.ofReal (gaussianConvolution (iidRowSumLaw μ v N) a t) := by
  rw [← gaussianRowNormalizer_eq_future μ v a ha]
  exact gaussianRowNormalizer_eq_convolution μ v N a ha t

#print axioms gaussianFutureWeight_eq_convolution
end SpectralRadiusUpperTail
