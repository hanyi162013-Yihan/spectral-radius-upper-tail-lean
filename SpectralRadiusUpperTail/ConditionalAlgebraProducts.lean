import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Normed.Algebra.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {A Ω : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A bounded predictable left factor can be pulled out of a centered
noncommutative increment; product integrability is proved here. -/
theorem conditional_algebra_left_zero (hm : m ≤ mΩ)
    {X D : Ω → A} (hX : Integrable X μ) (hD : StronglyMeasurable[m] D)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖D x‖ ≤ C) (hzero : μ[X | m] =ᵐ[μ] 0) :
    Integrable (fun x => D x * X x) μ ∧
      μ[fun x => D x * X x | m] =ᵐ[μ] 0 := by
  let B : A →L[ℝ] A →L[ℝ] A := ContinuousLinearMap.mul ℝ A
  have hi : Integrable (fun x => D x * X x) μ :=
    B.integrable_of_bilin_of_bdd_left C (hD.mono hm).aestronglyMeasurable hbound hX
  refine ⟨hi, ?_⟩
  filter_upwards [condExp_bilin_of_stronglyMeasurable_left B hD hi hX, hzero] with x hx hz
  change μ[fun x => D x * X x | m] x = 0
  simpa only [B, ContinuousLinearMap.mul_apply', hz, Pi.zero_apply, mul_zero] using hx

/-- The right-factor statement is separate: commutativity is not assumed. -/
theorem conditional_algebra_right_zero (hm : m ≤ mΩ)
    {X D : Ω → A} (hX : Integrable X μ) (hD : StronglyMeasurable[m] D)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖D x‖ ≤ C) (hzero : μ[X | m] =ᵐ[μ] 0) :
    Integrable (fun x => X x * D x) μ ∧
      μ[fun x => X x * D x | m] =ᵐ[μ] 0 := by
  let B : A →L[ℝ] A →L[ℝ] A := ContinuousLinearMap.mul ℝ A
  have hi : Integrable (fun x => X x * D x) μ :=
    B.integrable_of_bilin_of_bdd_right C hX (hD.mono hm).aestronglyMeasurable hbound
  refine ⟨hi, ?_⟩
  filter_upwards [condExp_bilin_of_stronglyMeasurable_right B hD hi hX, hzero] with x hx hz
  change μ[fun x => X x * D x | m] x = 0
  simpa only [B, ContinuousLinearMap.mul_apply', hz, Pi.zero_apply, zero_mul] using hx

#print axioms conditional_algebra_left_zero
#print axioms conditional_algebra_right_zero
end SpectralRadiusUpperTail
