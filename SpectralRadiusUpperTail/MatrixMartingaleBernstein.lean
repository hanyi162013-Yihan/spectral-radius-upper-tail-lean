import SpectralRadiusUpperTail.MatrixMartingaleNormTail
import SpectralRadiusUpperTail.BernsteinParameter

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Explicit Bernstein bound for the norm of a Hermitian martingale-difference sum. -/
theorem matrix_martingale_bernstein {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (n : ℕ) (t v : ℝ) (ht : 0 < t) (hv0 : 0 ≤ v)
    (hv : ∀ᵐ x ∂μ, ‖∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x‖ ≤ v) :
    μ.real {x | t ≤ ‖∑ i ∈ Finset.range n, X i x‖} ≤
      (2*(Fintype.card ι : ℝ)) * Real.exp (-t^2/(8*v+4*t)) := by
  have hs := bernstein_parameter hv0 ht
  have hb := matrix_martingale_norm_tail F X hX hXh hXn hzero hs.1 hs.2.1 n t v hv
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs.2.2)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))

#print axioms matrix_martingale_bernstein
end SpectralRadiusUpperTail
