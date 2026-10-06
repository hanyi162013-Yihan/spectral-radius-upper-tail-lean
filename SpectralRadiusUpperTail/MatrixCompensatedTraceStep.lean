import SpectralRadiusUpperTail.MatrixConditionalTraceExponential
import SpectralRadiusUpperTail.MatrixConditionalExponential

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Trace recursion for the actual conditional-square compensator.
The conditional exponential estimate is proved by the earlier theorem,
not included as an assumption here. -/
theorem matrix_compensated_trace_step {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {S X : Ω → Matrix ι ι 𝕂} (hS : StronglyMeasurable[m] S)
    (hSh : ∀ᵐ x ∂μ, (S x).IsHermitian) (C : ℝ) (hSn : ∀ᵐ x ∂μ, ‖S x‖ ≤ C)
    (hX : AEStronglyMeasurable X μ) (hXh : ∀ᵐ x ∂μ, (X x).IsHermitian)
    (hXn : ∀ᵐ x ∂μ, ‖X x‖ ≤ 1) (hzero : μ[X | m] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let D := μ[fun y => (X y)^2 | m]
    let B := fun x => s • X x-(2*s^2) • D x
    Integrable (fun x => RCLike.re (NormedSpace.exp (S x+B x)).trace) μ ∧
      ∀ᵐ x ∂μ, μ[fun y => RCLike.re (NormedSpace.exp (S y+B y)).trace | m] x ≤
        RCLike.re (NormedSpace.exp (S x)).trace := by
  let D : Ω → Matrix ι ι 𝕂 := μ[fun y => (X y)^2 | m]
  let B : Ω → Matrix ι ι 𝕂 := fun x => s • X x-(2*s^2) • D x
  have h2n : ∀ᵐ x ∂μ, ‖(X x)^2‖ ≤ 1 := by
    filter_upwards [hXn] with x hx
    have hh := norm_mul_le (X x) (X x)
    rw [← pow_two] at hh
    exact hh.trans (by nlinarith [norm_nonneg (X x)])
  have hi2 : Integrable (fun x => (X x)^2) μ := Integrable.of_bound (hX.pow 2) 1 h2n
  have hD := matrix_conditional_square_contraction hm hi2 hXh hXn
  have hDm : StronglyMeasurable[m] D := stronglyMeasurable_condExp
  have hBm : AEStronglyMeasurable B μ :=
    (hX.const_smul s).sub (((hDm.mono hm).aestronglyMeasurable).const_smul (2*s^2))
  have hBh : ∀ᵐ x ∂μ, (B x).IsHermitian := by
    filter_upwards [hXh,hD] with x hx hd
    exact (hx.smul (show IsSelfAdjoint s from rfl)).sub
      (hd.1.isHermitian.smul (show IsSelfAdjoint (2*s^2) from rfl))
  have hBn : ∀ᵐ x ∂μ, ‖B x‖ ≤ 1 := by
    filter_upwards [hXn,hD] with x hx hd
    exact compensated_increment_norm_le_one s (X x) (D x) hs hs1 hx hd.2
  have hmgf := matrix_conditional_compensated_exp hm hX hXh hXn hzero hs hs1
  exact matrix_conditional_trace_exp_step hm hS hBm hSh hBh C 1 hSn hBn hmgf.2

#print axioms matrix_compensated_trace_step
end SpectralRadiusUpperTail
