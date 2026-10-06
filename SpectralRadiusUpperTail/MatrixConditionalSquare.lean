import SpectralRadiusUpperTail.MatrixNormTransport
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

namespace SpectralRadiusUpperTail
open MeasureTheory Matrix
open scoped MeasureTheory Matrix.Norms.L2Operator ComplexOrder
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- The conditional square of a Hermitian contraction is a positive
semidefinite contraction, in the Euclidean operator norm. -/
theorem matrix_conditional_square_contraction {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X : Ω → Matrix ι ι 𝕂} (hX2 : Integrable (fun x => (X x)^2) μ)
    (hherm : ∀ᵐ x ∂μ, (X x).IsHermitian) (hbound : ∀ᵐ x ∂μ, ‖X x‖ ≤ 1) :
    ∀ᵐ x ∂μ, (μ[fun y => (X y)^2 | m] x).PosSemidef ∧
      ‖μ[fun y => (X y)^2 | m] x‖ ≤ 1 := by
  have hp : ∀ᵐ x ∂μ, ((X x)^2).PosSemidef := by
    filter_upwards [hherm] with x hx
    simpa only [pow_two, hx.eq] using (posSemidef_conjTranspose_mul_self (X x))
  have hn : ∀ᵐ x ∂μ, ‖(X x)^2‖ ≤ 1 := by
    filter_upwards [hbound] with x hx
    have hm : ‖(X x)^2‖ ≤ ‖X x‖*‖X x‖ := by
      simpa only [pow_two] using (norm_mul_le (X x) (X x))
    exact hm.trans (by nlinarith [norm_nonneg (X x)])
  have hc := (norm_condExp_le (fun x => (X x)^2) (m := m) (μ := μ)).trans
    (condExp_le_nonneg_const (m := m) zero_le_one hn)
  filter_upwards [matrixL2_condExp_posSemidef hm hX2 hp, hc] with x hx hy
  exact ⟨hx,hy⟩

#print axioms matrix_conditional_square_contraction
end SpectralRadiusUpperTail
