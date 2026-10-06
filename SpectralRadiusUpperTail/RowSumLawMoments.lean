import SpectralRadiusUpperTail.GaussianFutureConvolution
import SpectralRadiusUpperTail.RowNormalizerBound
import SpectralRadiusUpperTail.GaussianLogRatio

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

instance iidRowSumLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) : IsProbabilityMeasure (iidRowSumLaw μ v N) :=
  Measure.isProbabilityMeasure_map (iidRowSum_measurable v N).aemeasurable

lemma iidRowSumLaw_memLp (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ) :
    MemLp (fun x : 𝕂 => x) 2 (iidRowSumLaw μ v N) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (iidRowSum_measurable v N).aemeasurable).mpr
  exact iid_linear_row_memLp μ (fun i : Fin N => v i.val) hX

lemma iidRowSumLaw_mean (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) :
    (∫ x : 𝕂, x ∂iidRowSumLaw μ v N) = 0 := by
  rw [iidRowSumLaw, integral_map (f := fun x : 𝕂 => x)
    (iidRowSum_measurable v N).aemeasurable
    continuous_id.aestronglyMeasurable]
  exact iid_linear_row_mean μ (fun i : Fin N => v i.val) hX hm

lemma iidRowSumLaw_energy (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) :
    (∫ x : 𝕂, ‖x‖^2 ∂iidRowSumLaw μ v N) = ∑ i : Fin N, ‖v i.val‖^2 := by
  rw [iidRowSumLaw, integral_map (f := fun x : 𝕂 => ‖x‖^2)
    (iidRowSum_measurable v N).aemeasurable
    (continuous_norm.pow 2).aestronglyMeasurable]
  exact iid_linear_row_energy μ (fun i : Fin N => v i.val) hX hm hvar

/-- The logarithm of the actual recursive future integral satisfies the score
increment estimate. Only the future exponential-moment bound remains explicit;
probability normalization, mean and variance are derived from the entry law. -/
theorem gaussianFutureWeight_log_increment (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (N : ℕ) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) (iidRowSumLaw μ v N))
    (hL : (∫ x : 𝕂, Real.exp (c*‖x‖^2) ∂iidRowSumLaw μ v N) ≤ Real.exp L)
    (s h : 𝕂) :
    |Real.log (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N (s-h)).toReal -
      Real.log (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N s).toReal| ≤
        gaussianScoreConstant a c L*‖h‖*(1+‖s‖+‖h‖) := by
  have hXm := iidRowSumLaw_memLp μ v N hX
  have hmm := iidRowSumLaw_mean μ v N hX hm
  have hvm : (∫ x : 𝕂, ‖x‖^2 ∂iidRowSumLaw μ v N) ≤ 1 := by
    rw [iidRowSumLaw_energy μ v N hX hm hvar]
    exact hv
  have he (t : 𝕂) :
      (futureWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t).toReal =
        gaussianConvolution (iidRowSumLaw μ v N) a t := by
    rw [gaussianFutureWeight_eq_convolution μ v N a ha]
    exact ENNReal.toReal_ofReal (gaussianSoftTilt_basics _ hXm hmm a ha t).1.le
  rw [he (s-h), he s]
  exact gaussian_log_increment _ hXm hmm hvm a c L ha hc hLn hexp hL s h

#print axioms gaussianFutureWeight_log_increment
end SpectralRadiusUpperTail
