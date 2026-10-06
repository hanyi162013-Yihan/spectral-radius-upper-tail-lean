import SpectralRadiusUpperTail.MatrixCompensatedTraceStep

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- The actual compensated update decreases the expected trace exponential.
This is the finite-step integral inequality to iterate along the filtration. -/
theorem matrix_compensated_trace_integral_le {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {S X : Ω → Matrix ι ι 𝕂} (hS : StronglyMeasurable[m] S)
    (hSh : ∀ᵐ x ∂μ, (S x).IsHermitian) (C : ℝ) (hSn : ∀ᵐ x ∂μ, ‖S x‖ ≤ C)
    (hX : AEStronglyMeasurable X μ) (hXh : ∀ᵐ x ∂μ, (X x).IsHermitian)
    (hXn : ∀ᵐ x ∂μ, ‖X x‖ ≤ 1) (hzero : μ[X | m] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let D := μ[fun y => (X y)^2 | m]
    let B := fun x => s • X x-(2*s^2) • D x
    (∫ x, RCLike.re (NormedSpace.exp (S x+B x)).trace ∂μ) ≤
      ∫ x, RCLike.re (NormedSpace.exp (S x)).trace ∂μ := by
  let D : Ω → Matrix ι ι 𝕂 := μ[fun y => (X y)^2 | m]
  let B : Ω → Matrix ι ι 𝕂 := fun x => s • X x-(2*s^2) • D x
  have hstep := matrix_compensated_trace_step hm hS hSh C hSn hX hXh hXn hzero hs hs1
  have hiS := algebra_exp_integrable_of_bound (hS.mono hm).aestronglyMeasurable C hSn
  have hitS : Integrable (fun x => RCLike.re (NormedSpace.exp (S x)).trace) μ :=
    (matrixRealTrace : Matrix ι ι 𝕂 →L[ℝ] ℝ).integrable_comp hiS
  have hint := integral_mono_ae (integrable_condExp (μ := μ)
    (f := fun x => RCLike.re (NormedSpace.exp (S x+B x)).trace) (m := m)) hitS hstep.2
  rw [integral_condExp hm] at hint
  exact hint

#print axioms matrix_compensated_trace_integral_le
end SpectralRadiusUpperTail
