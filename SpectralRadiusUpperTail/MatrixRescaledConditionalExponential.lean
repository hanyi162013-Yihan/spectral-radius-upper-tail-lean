import SpectralRadiusUpperTail.MatrixConditionalExponential

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Transfer from the original finite-function conditional expectation
and normalize by a proved positive operator bound. The compensator in
the conclusion is the actual conditional square in operator norm. -/
theorem matrix_rescaled_conditional_exp {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {F : Ω → ι → ι → 𝕂} (hF : Integrable F μ)
    (hherm : ∀ᵐ x ∂μ, Matrix.IsHermitian (F x))
    (hzero : μ[F | m] =ᵐ[μ] 0) {b : ℝ} (hb : 0 < b)
    (hbound : ∀ᵐ x ∂μ, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕂) (F x)‖ ≤ b)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    let X : Ω → Matrix ι ι 𝕂 := fun x => b⁻¹ • matrixL2Equiv (F x)
    let D := μ[fun y => (X y)^2 | m]
    let B := fun x => s • X x-(2*s^2) • D x
    Integrable (fun x => NormedSpace.exp (B x)) μ ∧
      ∀ᵐ x ∂μ, μ[fun y => NormedSpace.exp (B y) | m] x ≤ 1 := by
  let T : (ι → ι → 𝕂) →L[ℝ] Matrix ι ι 𝕂 :=
    matrixL2Equiv.toContinuousLinearMap.restrictScalars ℝ
  let L : (ι → ι → 𝕂) →L[ℝ] Matrix ι ι 𝕂 := b⁻¹ • T
  have hi : Integrable (L ∘ F) μ := L.integrable_comp hF
  have hh : ∀ᵐ x ∂μ, ((L ∘ F) x).IsHermitian := by
    filter_upwards [hherm] with x hx
    exact hx.smul (show IsSelfAdjoint b⁻¹ from rfl)
  have hn : ∀ᵐ x ∂μ, ‖(L ∘ F) x‖ ≤ 1 := by
    filter_upwards [hbound] with x hx
    change ‖b⁻¹ • matrixL2Equiv (F x)‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb.le)]
    have ht : ‖matrixL2Equiv (F x)‖ = ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕂) (F x)‖ := rfl
    rw [ht]
    calc
      _ ≤ b⁻¹*b := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hz : μ[L ∘ F | m] =ᵐ[μ] 0 := by
    filter_upwards [L.comp_condExp_comm hF (m := m), hzero] with x hx hz
    change μ[L ∘ F | m] x = 0
    rw [← hx]
    simp only [Function.comp_apply, hz, Pi.zero_apply, map_zero]
  exact matrix_conditional_compensated_exp hm hi.aestronglyMeasurable hh hn hz hs hs1

#print axioms matrix_rescaled_conditional_exp
end SpectralRadiusUpperTail
