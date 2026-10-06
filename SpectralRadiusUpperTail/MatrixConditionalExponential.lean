import SpectralRadiusUpperTail.ConditionalCompensatedPolynomial
import SpectralRadiusUpperTail.AlgebraExponentialIntegrable
import SpectralRadiusUpperTail.MatrixConditionalSquare
import SpectralRadiusUpperTail.MatrixCompensatorOrder

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

theorem matrix_operator_condExp_mono {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F G : Ω → Matrix ι ι 𝕂} (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : ∀ᵐ x ∂μ, F x ≤ G x) :
    ∀ᵐ x ∂μ, μ[F | m] x ≤ μ[G | m] x := by
  have hp : ∀ᵐ x ∂μ, (G x-F x).PosSemidef :=
    hFG.mono fun _ hx => Matrix.le_iff.mp hx
  filter_upwards [matrixL2_condExp_posSemidef hm (hG.sub hF) hp,
    condExp_sub hG hF (m := m)] with x hx heq
  apply Matrix.le_iff.mpr
  simpa only [heq, Pi.sub_apply] using hx

/-- The compensated conditional matrix exponential bound. The variance
is the actual conditional square; measurability and the unit increment
bound imply all integrability needed by the proof. -/
theorem matrix_conditional_compensated_exp [Nonempty ι]
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → Matrix ι ι 𝕂} (hX : AEStronglyMeasurable X μ)
    (hherm : ∀ᵐ x ∂μ, (X x).IsHermitian) (hbound : ∀ᵐ x ∂μ, ‖X x‖ ≤ 1)
    (hzero : μ[X | m] =ᵐ[μ] 0) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let D := μ[fun y => (X y)^2 | m]
    let B := fun x => s • X x-(2*s^2) • D x
    Integrable (fun x => NormedSpace.exp (B x)) μ ∧
      ∀ᵐ x ∂μ, μ[fun y => NormedSpace.exp (B y) | m] x ≤ 1 := by
  let D : Ω → Matrix ι ι 𝕂 := μ[fun y => (X y)^2 | m]
  let B : Ω → Matrix ι ι 𝕂 := fun x => s • X x-(2*s^2) • D x
  have hiX : Integrable X μ := Integrable.of_bound hX 1 hbound
  have hX2bound : ∀ᵐ x ∂μ, ‖(X x)^2‖ ≤ 1 := by
    filter_upwards [hbound] with x hx
    have hmul := norm_mul_le (X x) (X x)
    rw [← pow_two] at hmul
    exact hmul.trans (by nlinarith [norm_nonneg (X x)])
  have hiX2 : Integrable (fun x => (X x)^2) μ :=
    Integrable.of_bound (hX.pow 2) 1 hX2bound
  have hD := matrix_conditional_square_contraction hm hiX2 hherm hbound
  have hDbound : ∀ᵐ x ∂μ, ‖D x‖ ≤ 1 := hD.mono fun _ hx => hx.2
  have hmD : StronglyMeasurable[m] D := stronglyMeasurable_condExp
  have hmB : AEStronglyMeasurable B μ :=
    (hX.const_smul s).sub (((hmD.mono hm).aestronglyMeasurable).const_smul (2*s^2))
  have hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ 1 := by
    filter_upwards [hbound, hDbound] with x hx hd
    exact compensated_increment_norm_le_one s (X x) (D x) hs hs1 hx hd
  have hBherm : ∀ᵐ x ∂μ, (B x).IsHermitian := by
    filter_upwards [hherm, hD] with x hx hd
    exact (hx.smul (show IsSelfAdjoint s from rfl)).sub
      (hd.1.isHermitian.smul (show IsSelfAdjoint (2*s^2) from rfl))
  have hiExp := algebra_exp_integrable_of_bound hmB 1 hBbound
  have hp := conditional_compensated_polynomial hm hiX hiX2 hzero 1 s hDbound
  have hle : ∀ᵐ x ∂μ, NormedSpace.exp (B x) ≤ 1+B x+(B x)^2 := by
    filter_upwards [hBherm,hBbound] with x hx hb
    exact matrix_exp_le_one_add_square hx hb
  have hce := matrix_operator_condExp_mono hm hiExp hp.1 hle
  change Integrable (fun x => NormedSpace.exp (B x)) μ ∧ _
  refine ⟨hiExp, ?_⟩
  filter_upwards [hce,hp.2,hD] with x hx he hd
  exact (hx.trans_eq he).trans (matrix_compensator_correction_le_one hd.1 hd.2 hs hs1)

#print axioms matrix_conditional_compensated_exp
end SpectralRadiusUpperTail
