import SpectralRadiusUpperTail.TalagrandInterpolationWeight
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The averaged scalar budget for the fiber induction. Both the observable
and its optimized exponential factor are genuinely integrable. -/
lemma talagrand_fiber_average_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : Ω → ℝ) (ha : Measurable a)
    (hrange : ∀ᵐ x ∂μ, 0 ≤ a x ∧ a x ≤ 1) (hmean : 0 < ∫ x, a x ∂μ) :
    Integrable a μ ∧
    Integrable (fun x => Real.exp (-talagrandWeight (a x)*Real.log (a x)+
      (1-talagrandWeight (a x))^2/4)) μ ∧
    (∫ x, Real.exp (-talagrandWeight (a x)*Real.log (a x)+
      (1-talagrandWeight (a x))^2/4) ∂μ) ≤ 1/(∫ x, a x ∂μ) := by
  have hi : Integrable a μ := by
    apply (integrable_const (1 : ℝ)).mono' ha.aestronglyMeasurable
    filter_upwards [hrange] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  let g := fun x => Real.exp (-talagrandWeight (a x)*Real.log (a x)+(1-talagrandWeight (a x))^2/4)
  have hw : Measurable (fun x => talagrandWeight (a x)) := talagrandWeight_measurable.comp ha
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hbound : ∀ᵐ x ∂μ, g x ≤ 2-a x := by
    filter_upwards [hrange] with x hx
    exact talagrandWeight_mixing_bound (a x) hx.1 hx.2
  have hgi : Integrable g μ := by
    apply (integrable_const (2 : ℝ)).mono' hg.aestronglyMeasurable
    filter_upwards [hrange, hbound] with x hx hb
    have hpos : 0 ≤ g x := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    linarith
  refine ⟨hi, hgi, ?_⟩
  have he := integral_mono_ae hgi ((integrable_const (2 : ℝ)).sub hi) hbound
  change (∫ x, g x ∂μ) ≤ ∫ x, 2-a x ∂μ at he
  rw [integral_sub (integrable_const (2 : ℝ)) hi, integral_const] at he
  simp only [probReal_univ, smul_eq_mul, one_mul] at he
  exact he.trans (talagrand_scalar_average_budget (∫ x, a x ∂μ) hmean)

#print axioms talagrand_fiber_average_budget
end SpectralRadiusUpperTail
