import SpectralRadiusUpperTail.SchurRawGapScaling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem schurSquaredGapLaw_raw_lintegral
    (n y : ℝ) (hn : 0 < n) (hy : 0 < y) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂schurSquaredGapLaw n y) =
      (ENNReal.ofReal (n/2)/schurGapKernelNormalizer n y)*
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (schurRawGapKernel n y s)*F s := by
  simpa only [schurRawGapKernel_ofReal] using schurSquaredGapLaw_lintegral_kernel n y hn hy F hF

theorem schurRawGapKernel_lintegral_normalized
    (n y : ℝ) (hn : 0 < n) (hy : 0 < y) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (schurRawGapKernel n y s)*F s) =
      ((ENNReal.ofReal (n/2))⁻¹*schurGapKernelNormalizer n y)*
        ∫⁻ s, F s ∂schurSquaredGapLaw n y := by
  simpa only [schurRawGapKernel_ofReal] using schurGap_raw_lintegral_eq_normalized n y hn hy F hF

/-- Scaling the matrix by c^(-1/2) scales squared gaps by c^(-1),
changes precision n to n*c, and scales the imaginary part accordingly.
Normalization follows from total probability mass, so no new normalizer
integral needs to be evaluated. -/
theorem schurSquaredGapLaw_map_div (n y c : ℝ) (hn : 0 < n) (hy : 0 < y) (hc : 0 < c) :
    (schurSquaredGapLaw n y).map (fun s : ℝ => s/c)=
      schurSquaredGapLaw (n*c) (y/Real.sqrt c) := by
  have hnc : 0 < n*c := mul_pos hn hc
  have hyc : 0 < y/Real.sqrt c := div_pos hy (Real.sqrt_pos.mpr hc)
  let := schurSquaredGapLaw_probability n y hn hy
  let := schurSquaredGapLaw_probability (n*c) (y/Real.sqrt c) hnc hyc
  let K := (ENNReal.ofReal (n/2)/schurGapKernelNormalizer n y)*
    (ENNReal.ofReal (Real.sqrt c)*
      ((ENNReal.ofReal ((n*c)/2))⁻¹*schurGapKernelNormalizer (n*c) (y/Real.sqrt c)))
  have he (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
      (∫⁻ s, F (s/c) ∂schurSquaredGapLaw n y)=
        K*∫⁻ s, F s ∂schurSquaredGapLaw (n*c) (y/Real.sqrt c) := by
    have hm : Measurable (fun s : ℝ => F (s/c)) := hF.comp (by fun_prop)
    rw [schurSquaredGapLaw_raw_lintegral n y hn hy (fun s => F (s/c)) hm,
      schurRawGapKernel_scale_lintegral n y c hc F hF,
      schurRawGapKernel_lintegral_normalized (n*c) (y/Real.sqrt c) hnc hyc F hF]
    dsimp only [K]
    ac_rfl
  have hK : K=1 := by
    have hh := he (fun _ => 1) measurable_const
    simpa only [lintegral_const,measure_univ,mul_one] using hh.symm
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (show Measurable (fun s : ℝ => s/c) by fun_prop),he F hF,hK,one_mul]

#print axioms schurSquaredGapLaw_raw_lintegral
#print axioms schurRawGapKernel_lintegral_normalized
#print axioms schurSquaredGapLaw_map_div
end SpectralRadiusUpperTail
