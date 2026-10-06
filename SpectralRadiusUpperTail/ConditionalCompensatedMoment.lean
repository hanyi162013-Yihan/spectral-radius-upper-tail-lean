import SpectralRadiusUpperTail.ConditionalAlgebraProducts
import SpectralRadiusUpperTail.MatrixCompensatedAlgebra

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {A Ω : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The conditional second moment of the compensated increment, with
the compensator defined to be the actual conditional square. -/
theorem conditional_compensated_square (hm : m ≤ mΩ) {X : Ω → A}
    (hX : Integrable X μ) (hX2 : Integrable (fun x => (X x)^2) μ)
    (hzero : μ[X | m] =ᵐ[μ] 0) (C s : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖μ[fun y => (X y)^2 | m] x‖ ≤ C) :
    let D := μ[fun y => (X y)^2 | m]
    Integrable (fun x => (s • X x-(2*s^2) • D x)^2) μ ∧
      μ[fun x => (s • X x-(2*s^2) • D x)^2 | m] =ᵐ[μ]
        (fun x => s^2 • D x+(4*s^4) • (D x)^2) := by
  let Y : Ω → A := fun x => (X x)^2
  have hiY : Integrable Y μ := hX2
  let D : Ω → A := μ[Y | m]
  let Z : Ω → A := fun x => X x*D x+D x*X x
  let Q : Ω → A := fun x => (D x)^2
  have hD : StronglyMeasurable[m] D := stronglyMeasurable_condExp
  have hiD : Integrable D μ := integrable_condExp
  have hl := conditional_algebra_left_zero hm hX hD C hbound hzero
  have hr := conditional_algebra_right_zero hm hX hD C hbound hzero
  have hiZ : Integrable Z μ := hr.1.add hl.1
  have hz : μ[Z | m] =ᵐ[μ] 0 := by
    filter_upwards [condExp_add hr.1 hl.1 m, hr.2, hl.2] with x hx hxr hxl
    change μ[(fun x => X x*D x)+(fun x => D x*X x) | m] x = 0
    simpa only [Pi.add_apply, hxr, hxl, Pi.zero_apply, add_zero] using hx
  have hiQ : Integrable Q μ := by
    have hh := (ContinuousLinearMap.mul ℝ A).integrable_of_bilin_of_bdd_left
      C (hD.mono hm).aestronglyMeasurable hbound hiD
    simpa only [Q, pow_two, ContinuousLinearMap.mul_apply'] using hh
  have heQ : μ[Q | m] = Q :=
    condExp_of_stronglyMeasurable hm (hD.pow 2) hiQ
  let P : Ω → A := s^2 • Y-(2*s^3) • Z+(4*s^4) • Q
  have heP : (fun x => (s • X x-(2*s^2) • D x)^2) = P := by
    funext x
    exact compensated_noncommutative_square s (X x) (D x)
  have hiP : Integrable P μ :=
    ((hiY.smul (s^2)).sub (hiZ.smul (2*s^3))).add (hiQ.smul (4*s^4))
  change Integrable (fun x => (s • X x-(2*s^2) • D x)^2) μ ∧ _
  rw [heP]
  refine ⟨hiP, ?_⟩
  filter_upwards [condExp_add ((hiY.smul (s^2)).sub (hiZ.smul (2*s^3)))
      (hiQ.smul (4*s^4)) m,
    condExp_sub (hiY.smul (s^2)) (hiZ.smul (2*s^3)) (m := m),
    condExp_smul (s^2) Y m (μ := μ), condExp_smul (2*s^3) Z m (μ := μ),
    condExp_smul (4*s^4) Q m (μ := μ), hz] with x hp hsub hy hz' hq hz0
  change μ[P | m] x = s^2 • D x+(4*s^4) • Q x
  simpa only [P, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hsub,
    hy, hz', hq, heQ, hz0, Pi.zero_apply, smul_zero, sub_zero] using hp

#print axioms conditional_compensated_square
end SpectralRadiusUpperTail
