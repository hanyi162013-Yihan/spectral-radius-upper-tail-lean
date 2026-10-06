import SpectralRadiusUpperTail.DensityCost
import SpectralRadiusUpperTail.Centering

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Weighted density variation controls an actual, integrable coupling error. -/
theorem densityCoupling_difference_moments (μ : Measure E) [IsProbabilityMeasure μ]
    (k : E → ℝ) (hk : Measurable k) (hk_nonneg : ∀ x, 0 ≤ k x)
    (hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1)
    (hw : Integrable (fun x => |k x-1| * ‖x‖ ^ 2) μ) :
    let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
    Integrable (fun z : E × E => z.1-z.2) π ∧
      Integrable (fun z : E × E => ‖z.1-z.2‖ ^ 2) π ∧
      (∫ z, ‖z.1-z.2‖ ^ 2 ∂π) ≤ 2 * ∫ x, |k x-1| * ‖x‖ ^ 2 ∂μ := by
  let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
  have : IsProbabilityMeasure π := densityCoupling_probability μ _ hk.ennreal_ofReal hnorm
  have hX : AEStronglyMeasurable (fun z : E × E => z.1-z.2) π :=
    (continuous_fst.sub continuous_snd).measurable.aestronglyMeasurable
  have hX2 : AEStronglyMeasurable (fun z : E × E => ‖z.1-z.2‖ ^ 2) π :=
    ((continuous_fst.sub continuous_snd).norm.pow 2).measurable.aestronglyMeasurable
  have hnX : 0 ≤ᵐ[π] (fun z : E × E => ‖z.1-z.2‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hnw : 0 ≤ᵐ[μ] (fun x => |k x-1| * ‖x‖ ^ 2) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hbound := densityCoupling_secondMoment_le μ k hk hk_nonneg hnorm
  have hwfin := (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable hnw).mpr hw
  have hXfin : (∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖ ^ 2) ∂π) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hwfin) hbound
  have hX2int := (lintegral_ofReal_ne_top_iff_integrable hX2 hnX).mp hXfin
  have hXint : Integrable (fun z : E × E => z.1-z.2) π :=
    MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
      ((memLp_two_iff_integrable_sq_norm hX).mpr hX2int)
  refine ⟨hXint, hX2int, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (integral_nonneg_of_ae hnw))).mp
  rw [ofReal_integral_eq_lintegral_ofReal hX2int hnX,
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ofReal_integral_eq_lintegral_ofReal hw hnw]
  exact hbound

/-- Centering by the actual mean preserves the weighted total-variation bound.
This applies in particular to real and complex scalar entries. -/
theorem densityCoupling_centered_secondMoment_le (μ : Measure E) [IsProbabilityMeasure μ]
    (k : E → ℝ) (hk : Measurable k) (hk_nonneg : ∀ x, 0 ≤ k x)
    (hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1)
    (hw : Integrable (fun x => |k x-1| * ‖x‖ ^ 2) μ) :
    let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
    (∫ z, ‖(z.1-z.2) - ∫ w, w.1-w.2 ∂π‖ ^ 2 ∂π) ≤
      2 * ∫ x, |k x-1| * ‖x‖ ^ 2 ∂μ := by
  let π := densityCoupling μ (fun x => ENNReal.ofReal (k x))
  have : IsProbabilityMeasure π := densityCoupling_probability μ _ hk.ennreal_ofReal hnorm
  have hm := densityCoupling_difference_moments μ k hk hk_nonneg hnorm hw
  exact (integral_centered_norm_sq_le π (fun z => z.1-z.2) hm.1 hm.2.1).trans hm.2.2

#print axioms densityCoupling_difference_moments
#print axioms densityCoupling_centered_secondMoment_le
end SpectralRadiusUpperTail
