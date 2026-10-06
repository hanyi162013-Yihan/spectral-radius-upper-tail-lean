import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Positive scalar substitution on the positive real ray. -/
theorem positiveRay_scale_lintegral (c : ℝ) (hc : 0 < c)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s in Set.Ioi (0 : ℝ), F s) =
      ENNReal.ofReal c*(∫⁻ t in Set.Ioi (0 : ℝ), F (c*t)) := by
  have hpre : (fun t : ℝ => c*t) ⁻¹' Set.Ioi (0 : ℝ)=Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_preimage,Set.mem_Ioi,mul_pos_iff_of_pos_left hc]
  have hm := congrArg (fun μ : Measure ℝ => μ.restrict (Set.Ioi (0 : ℝ)))
    (Real.smul_map_volume_mul_left hc.ne')
  rw [Measure.restrict_smul,Measure.restrict_map (by fun_prop) measurableSet_Ioi,hpre,
    abs_of_pos hc] at hm
  have hh := congrArg (fun μ : Measure ℝ => ∫⁻ s, F s ∂μ) hm
  rw [lintegral_smul_measure,smul_eq_mul,lintegral_map hF (by fun_prop)] at hh
  exact hh.symm

#print axioms positiveRay_scale_lintegral
end SpectralRadiusUpperTail
