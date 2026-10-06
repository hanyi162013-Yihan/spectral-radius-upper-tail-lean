import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma log_integral_error_of_uniform_log_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hi : Integrable f μ) (hp : ∀ x, 0 < f x)
    (A E : ℝ) (h : ∀ x, |Real.log (f x)-A| ≤ E) :
    |Real.log (∫ x, f x ∂μ)-A| ≤ E := by
  have hlo (x : Ω) : Real.exp (A-E) ≤ f x := by
    rw [← Real.exp_log (hp x)]
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp (h x)).1
    linarith
  have hhi (x : Ω) : f x ≤ Real.exp (A+E) := by
    rw [← Real.exp_log (hp x)]
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp (h x)).2
    linarith
  have hli : Real.exp (A-E) ≤ ∫ x, f x ∂μ := by
    simpa using integral_mono (integrable_const (Real.exp (A-E))) hi hlo
  have hui : (∫ x, f x ∂μ) ≤ Real.exp (A+E) := by
    simpa using integral_mono hi (integrable_const (Real.exp (A+E))) hhi
  have hpi : 0 < ∫ x, f x ∂μ := (Real.exp_pos _).trans_le hli
  have hl := Real.log_le_log (Real.exp_pos (A-E)) hli
  have hu := Real.log_le_log hpi hui
  rw [Real.log_exp] at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms log_integral_error_of_uniform_log_error
end SpectralRadiusUpperTail
