import SpectralRadiusUpperTail.MarkedNonrealKernelScaling

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal

theorem markedNonrealRawKernel_scaled_lintegral
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z : ℂ in {z | 0 < z.im}, markedNonrealRawKernel m z*
      g ((Real.sqrt (m+2 : ℝ))⁻¹ • z)) =
      ENNReal.ofReal Real.pi*∫⁻ z : ℂ in {z | 0 < z.im},
        ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z)*g z := by
  let c := Real.sqrt (m+2 : ℝ)
  let S : Set ℂ := {z | 0 < z.im}
  let H := S.indicator (fun z => markedNonrealRawKernel m z*g (c⁻¹ • z))
  let K := S.indicator (fun z => ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z)*g z)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c^2=(m+2 : ℝ) := Real.sq_sqrt (by positivity)
  have hS : MeasurableSet S := measurableSet_lt measurable_const Complex.continuous_im.measurable
  have hH : Measurable H := ((markedNonrealRawKernel_measurable m).mul
    (hg.comp (by fun_prop))).indicator hS
  have hp (z : ℂ) : ENNReal.ofReal (m+2 : ℝ)*H (c • z)=ENNReal.ofReal Real.pi*K z := by
    have hi : c • z ∈ S ↔ z ∈ S := by
      change 0 < (c • z).im ↔ 0 < z.im
      simp [Complex.smul_im,smul_eq_mul,mul_pos_iff_of_pos_left hc]
    by_cases hz : z ∈ S
    · rw [show H (c • z)=markedNonrealRawKernel m (c • z)*g (c⁻¹ • (c • z))
        from Set.indicator_of_mem (hi.mpr hz) _,
        show K z=ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z)*g z
        from Set.indicator_of_mem hz _]
      rw [smul_smul,inv_mul_cancel₀ hc.ne',one_smul,← mul_assoc]
      rw [markedNonrealRawKernel_scaled]
      exact mul_assoc _ _ _
    · dsimp only [H,K]
      rw [Set.indicator_of_notMem (not_congr hi |>.mpr hz),Set.indicator_of_notMem hz]
      simp only [mul_zero]
  calc
    _ = ∫⁻ z : ℂ, H z := (lintegral_indicator hS _).symm
    _ = ENNReal.ofReal (c^2)*∫⁻ z : ℂ, H (c • z) := complex_scale_lintegral c hc H hH
    _ = ∫⁻ z : ℂ, ENNReal.ofReal Real.pi*K z := by
      rw [hc2,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr hp
    _ = ENNReal.ofReal Real.pi*∫⁻ z : ℂ, K z :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_indicator hS]

theorem markedNonrealPairTestIntegral_scale
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    markedNonrealPairTestIntegral m (fun z => g ((1/Real.sqrt (m+2 : ℝ)) • z))=
      ENNReal.ofReal (4*Real.pi^2)*∫⁻ z : ℂ in {z | 0 < z.im},
        ENNReal.ofReal (realGinibreNonrealDensityAt (m+2) z)*g z := by
  rw [markedNonrealPairTestIntegral_eq_density m
    (fun z => g ((1/Real.sqrt (m+2 : ℝ)) • z)) (hg.comp (by fun_prop))]
  simp only [one_div]
  rw [markedNonrealRawKernel_scaled_lintegral m g hg,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*Real.pi)]
  congr 2
  ring

#print axioms markedNonrealRawKernel_scaled_lintegral
#print axioms markedNonrealPairTestIntegral_scale
end SpectralRadiusUpperTail
