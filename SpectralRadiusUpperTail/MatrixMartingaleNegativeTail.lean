import SpectralRadiusUpperTail.MatrixMartingaleSpectralTail

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Negated increments have the same actual conditional squares and yield the other spectral tail. -/
theorem matrix_martingale_negative_spectral_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) (t v : ℝ)
    (hv : ∀ᵐ x ∂μ, ‖∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x‖ ≤ v) :
    μ.real {x | ∃ l ∈ spectrum ℝ (-(∑ i ∈ Finset.range n, X i x)), t ≤ l} ≤
      (Fintype.card ι : ℝ) * Real.exp (-s*t+2*s^2*v) := by
  have hm : ∀ i, StronglyMeasurable[F (i+1)] (fun x => -X i x) := fun i => (hX i).neg
  have hh : ∀ i, ∀ᵐ x ∂μ, (-X i x).IsHermitian := by
    intro i
    filter_upwards [hXh i] with x hx
    exact hx.neg
  have hn : ∀ i, ∀ᵐ x ∂μ, ‖-X i x‖ ≤ 1 := by
    intro i
    simpa only [norm_neg] using hXn i
  have hz : ∀ i, μ[fun x => -X i x | F i] =ᵐ[μ] 0 := by
    intro i
    filter_upwards [condExp_neg (μ := μ) (X i) (F i), hzero i] with x hx hy
    change μ[-X i | F i] x = 0
    rw [hx, Pi.neg_apply, hy, Pi.zero_apply, neg_zero]
  have hv' : ∀ᵐ x ∂μ, ‖∑ i ∈ Finset.range n,
      μ[fun y => (-X i y)^2 | F i] x‖ ≤ v := by
    simpa only [neg_sq] using hv
  have ht := matrix_martingale_spectral_tail F (fun i x => -X i x)
    hm hh hn hz hs hs1 n t v hv'
  simpa only [Finset.sum_neg_distrib] using ht

#print axioms matrix_martingale_negative_spectral_tail
end SpectralRadiusUpperTail
