import SpectralRadiusUpperTail.TalagrandFiberBudget
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The last scalar averaging step of the Talagrand product induction.
Once each head fiber has the displayed inner-integral bound, its mean
closes exactly at the reciprocal of the full target probability. -/
theorem talagrand_averaged_fiber_step
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (pB : ℝ) (hpB : 0 < pB)
    (a J : Ω → ℝ) (ha : Measurable a)
    (hrange : ∀ᵐ x ∂μ, 0 ≤ a x ∧ a x ≤ 1)
    (hmean : 0 < ∫ x, a x ∂μ)
    (hJi : Integrable J μ)
    (hJ : ∀ᵐ x ∂μ,
      J x ≤ (1/pB)*Real.exp
        (-talagrandWeight (a x)*Real.log (a x)+
          (1-talagrandWeight (a x))^2/4)) :
    pB*(∫ x, a x ∂μ)*(∫ x, J x ∂μ) ≤ 1 := by
  obtain ⟨_, hgi, hbudget⟩ :=
    talagrand_fiber_average_budget μ a ha hrange hmean
  let g := fun x => Real.exp
    (-talagrandWeight (a x)*Real.log (a x)+
      (1-talagrandWeight (a x))^2/4)
  have hinner : (∫ x, J x ∂μ) ≤ (1/pB)*(∫ x, g x ∂μ) := by
    have hh := integral_mono_ae hJi (hgi.const_mul (1/pB)) hJ
    simpa only [integral_const_mul] using hh
  have hbound : (∫ x, J x ∂μ) ≤
      (1/pB)*(1/(∫ x, a x ∂μ)) :=
    hinner.trans (mul_le_mul_of_nonneg_left hbudget (by positivity))
  calc
    pB*(∫ x, a x ∂μ)*(∫ x, J x ∂μ) ≤
        pB*(∫ x, a x ∂μ)*((1/pB)*(1/(∫ x, a x ∂μ))) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hpB.le hmean.le)
    _ = 1 := by
      field_simp

#print axioms talagrand_averaged_fiber_step
end SpectralRadiusUpperTail
