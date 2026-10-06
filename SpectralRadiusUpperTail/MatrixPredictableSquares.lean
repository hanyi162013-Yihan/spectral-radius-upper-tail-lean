import SpectralRadiusUpperTail.MatrixCompensatedStateTrace

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Hermitian structure of both actual finite sums used in compensation. -/
lemma matrix_predictable_sums_hermitian {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1) (n : ℕ) :
    ∀ᵐ x ∂μ, (∑ i ∈ Finset.range n, X i x).IsHermitian ∧
      (∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x).IsHermitian := by
  have hD : ∀ i, ∀ᵐ x ∂μ, (μ[fun y => (X i y)^2 | F i] x).IsHermitian := by
    intro i
    have hm : AEStronglyMeasurable (X i) μ :=
      ((hX i).mono (F.le (i+1))).aestronglyMeasurable
    have hn : ∀ᵐ x ∂μ, ‖(X i x)^2‖ ≤ 1 := by
      filter_upwards [hXn i] with x hx
      have hh := norm_mul_le (X i x) (X i x)
      rw [← pow_two] at hh
      exact hh.trans (by nlinarith [norm_nonneg (X i x)])
    have hd := matrix_conditional_square_contraction (F.le i)
      (Integrable.of_bound (hm.pow 2) 1 hn) (hXh i) (hXn i)
    filter_upwards [hd] with x hx
    exact hx.1.isHermitian
  filter_upwards [ae_all_iff.mpr hXh, ae_all_iff.mpr hD] with x hx hd
  constructor
  · exact isSelfAdjoint_sum _ (fun i _ => hx i)
  · exact isSelfAdjoint_sum _ (fun i _ => hd i)

#print axioms matrix_predictable_sums_hermitian
end SpectralRadiusUpperTail
