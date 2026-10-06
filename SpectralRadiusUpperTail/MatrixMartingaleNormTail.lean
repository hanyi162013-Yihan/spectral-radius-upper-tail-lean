import SpectralRadiusUpperTail.MatrixMartingaleNegativeTail
import SpectralRadiusUpperTail.MatrixNormSpectralEvent

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Two-sided operator-norm concentration using the actual predictable variance.
The factor is twice the matrix dimension. -/
theorem matrix_martingale_norm_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) (t v : ℝ)
    (hv : ∀ᵐ x ∂μ, ‖∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x‖ ≤ v) :
    μ.real {x | t ≤ ‖∑ i ∈ Finset.range n, X i x‖} ≤
      (2*(Fintype.card ι : ℝ)) * Real.exp (-s*t+2*s^2*v) := by
  let A : Set Ω := {x | ∃ l ∈ spectrum ℝ (∑ i ∈ Finset.range n, X i x), t ≤ l}
  let B : Set Ω := {x | ∃ l ∈ spectrum ℝ (-(∑ i ∈ Finset.range n, X i x)), t ≤ l}
  have hh := matrix_predictable_sums_hermitian F X hX hXh hXn n
  have hsub : {x | t ≤ ‖∑ i ∈ Finset.range n, X i x‖} ≤ᵐ[μ] (A ∪ B : Set Ω) := by
    filter_upwards [hh] with x hx
    intro ht
    exact matrix_norm_spectral_event hx.1 ht
  have hp := matrix_martingale_spectral_tail F X hX hXh hXn hzero hs hs1 n t v hv
  have hn := matrix_martingale_negative_spectral_tail F X hX hXh hXn hzero hs hs1 n t v hv
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hu := (measureReal_union_le (μ := μ) A B).trans (add_le_add hp hn)
  have ht := hm.trans hu
  have he : (Fintype.card ι : ℝ)*Real.exp (-s*t+2*s^2*v)+
      (Fintype.card ι : ℝ)*Real.exp (-s*t+2*s^2*v) =
        (2*(Fintype.card ι : ℝ))*Real.exp (-s*t+2*s^2*v) := by ring
  rw [he] at ht
  exact ht

#print axioms matrix_martingale_norm_tail
end SpectralRadiusUpperTail
