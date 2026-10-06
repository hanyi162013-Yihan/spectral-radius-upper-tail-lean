import SpectralRadiusUpperTail.PositiveRayScaleLIntegral
import SpectralRadiusUpperTail.SchurGapKernelLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def schurRawGapKernel (n y s : ℝ) : ℝ :=
  Real.exp (-(n/2)*s)*(Real.sqrt (s+4*y^2))⁻¹

theorem schurRawGapKernel_measurable (n y : ℝ) : Measurable (schurRawGapKernel n y) := by
  unfold schurRawGapKernel
  fun_prop

theorem schurRawGapKernel_ofReal (n y s : ℝ) :
    ENNReal.ofReal (schurRawGapKernel n y s)=
      ENNReal.ofReal (Real.exp (-(n/2)*s))*ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) :=
  ENNReal.ofReal_mul (Real.exp_pos _).le

theorem schurRawGapKernel_scale (n y c s : ℝ) (hc : 0 < c) :
    schurRawGapKernel n y (c*s) =
      (Real.sqrt c)⁻¹*schurRawGapKernel (n*c) (y/Real.sqrt c) s := by
  have hr : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have he : c*s+4*y^2=c*(s+4*(y/Real.sqrt c)^2) := by
    rw [div_pow,Real.sq_sqrt hc.le]
    field_simp
  unfold schurRawGapKernel
  rw [he,Real.sqrt_mul hc.le,mul_inv_rev,
    show -(n/2)*(c*s)=-((n*c)/2)*s by ring]
  ring

theorem schurRawGapKernel_scale_lintegral (n y c : ℝ) (hc : 0 < c)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (schurRawGapKernel n y s)*F (s/c)) =
      ENNReal.ofReal (Real.sqrt c)*
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (schurRawGapKernel (n*c) (y/Real.sqrt c) s)*F s := by
  have hm : Measurable (fun s => ENNReal.ofReal (schurRawGapKernel n y s)*F (s/c)) :=
    (schurRawGapKernel_measurable n y).ennreal_ofReal.mul (hF.comp (by fun_prop))
  rw [positiveRay_scale_lintegral c hc
    (fun s => ENNReal.ofReal (schurRawGapKernel n y s)*F (s/c)) hm]
  simp_rw [schurRawGapKernel_scale n y c _ hc,mul_div_cancel_left₀ _ hc.ne',
    ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg c)),mul_assoc,
    lintegral_const_mul' (ENNReal.ofReal ((Real.sqrt c)⁻¹)) _ ENNReal.ofReal_ne_top]
  rw [← mul_assoc,← ENNReal.ofReal_mul hc.le]
  congr 1
  have hr : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hh : c*(Real.sqrt c)⁻¹=Real.sqrt c := by
    nth_rw 1 [← Real.sq_sqrt hc.le]
    rw [pow_two,mul_assoc,mul_inv_cancel₀ hr,mul_one]
  rw [hh]

#print axioms schurRawGapKernel_scale
#print axioms schurRawGapKernel_scale_lintegral
end SpectralRadiusUpperTail
