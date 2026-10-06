import SpectralRadiusUpperTail.ConditionalCompensatedMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {A Ω : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The full quadratic exponential majorant has an explicit conditional
mean for the actual conditional-square compensator. -/
theorem conditional_compensated_polynomial (hm : m ≤ mΩ) {X : Ω → A}
    (hX : Integrable X μ) (hX2 : Integrable (fun x => (X x)^2) μ)
    (hzero : μ[X | m] =ᵐ[μ] 0) (C s : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖μ[fun y => (X y)^2 | m] x‖ ≤ C) :
    let D := μ[fun y => (X y)^2 | m]
    let B := fun x => s • X x-(2*s^2) • D x
    Integrable (fun x => 1+B x+(B x)^2) μ ∧
      μ[fun x => 1+B x+(B x)^2 | m] =ᵐ[μ]
        (fun x => 1-s^2 • D x+(4*s^4) • (D x)^2) := by
  let D : Ω → A := μ[fun y => (X y)^2 | m]
  let B : Ω → A := s • X-(2*s^2) • D
  have hiD : Integrable D μ := integrable_condExp
  have hD : StronglyMeasurable[m] D := stronglyMeasurable_condExp
  have heD : μ[D | m] = D := condExp_of_stronglyMeasurable hm hD hiD
  have hiB : Integrable B μ := (hX.smul s).sub (hiD.smul (2*s^2))
  have heB : μ[B | m] =ᵐ[μ] fun x => -(2*s^2) • D x := by
    filter_upwards [condExp_sub (hX.smul s) (hiD.smul (2*s^2)) (m := m),
      condExp_smul s X m (μ := μ), condExp_smul (2*s^2) D m (μ := μ),
      hzero] with x hx hsX hsD hz
    change μ[s • X-(2*s^2) • D | m] x = -(2*s^2) • D x
    simpa only [Pi.sub_apply, hsX, hsD, heD, Pi.smul_apply, hz,
      Pi.zero_apply, smul_zero, zero_sub, neg_smul] using hx
  have hb := conditional_compensated_square hm hX hX2 hzero C s hbound
  have hiB2 : Integrable (fun x => (B x)^2) μ := hb.1
  have heB2 : μ[fun x => (B x)^2 | m] =ᵐ[μ]
      fun x => s^2 • D x+(4*s^4) • (D x)^2 := hb.2
  have hi1 : Integrable (fun _ : Ω => (1 : A)) μ := integrable_const 1
  have he1 : μ[(fun _ : Ω => (1 : A)) | m] = fun _ => 1 :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_const hi1
  change Integrable (fun x => 1+B x+(B x)^2) μ ∧ _
  refine ⟨(hi1.add hiB).add hiB2, ?_⟩
  filter_upwards [condExp_add (hi1.add hiB) hiB2 m, condExp_add hi1 hiB m,
    heB, heB2] with x hp h1 hb1 hb2
  change μ[(fun _ : Ω => (1 : A))+B+(fun x => (B x)^2) | m] x = _
  calc
    _ = 1+(-(2*s^2) • D x)+(s^2 • D x+(4*s^4) • (D x)^2) := by
      simpa only [Pi.add_apply, h1, he1, hb1, hb2] using hp
    _ = _ := by module

#print axioms conditional_compensated_polynomial
end SpectralRadiusUpperTail
