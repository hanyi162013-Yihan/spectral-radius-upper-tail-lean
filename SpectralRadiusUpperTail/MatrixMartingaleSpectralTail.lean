import SpectralRadiusUpperTail.MatrixCompensatedSpectralTail
import SpectralRadiusUpperTail.MatrixVarianceCompensation
import SpectralRadiusUpperTail.MatrixPredictableSquares

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Spectral tail for the uncorrected sum of Hermitian martingale differences,
using the norm bound on their actual total conditional square. -/
theorem matrix_martingale_spectral_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) (t v : ℝ)
    (hv : ∀ᵐ x ∂μ, ‖∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x‖ ≤ v) :
    μ.real {x | ∃ l ∈ spectrum ℝ (∑ i ∈ Finset.range n, X i x), t ≤ l} ≤
      (Fintype.card ι : ℝ) * Real.exp (-s*t+2*s^2*v) := by
  have hh := matrix_predictable_sums_hermitian F X hX hXh hXn n
  have hsub : {x | ∃ l ∈ spectrum ℝ (∑ i ∈ Finset.range n, X i x), t ≤ l}
      ≤ᵐ[μ] {x | ∃ r ∈ spectrum ℝ (matrixCompensatedState μ F X s n x),
        s*t-2*s^2*v ≤ r} := by
    filter_upwards [hh, hv] with x hx hvx
    intro ht
    change ∃ r ∈ spectrum ℝ (matrixCompensatedState μ F X s n x), s*t-2*s^2*v ≤ r
    rw [matrixCompensatedState_eq]
    exact matrix_variance_compensation hx.1 hx.2 hs
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg s)) hvx ht
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have ht := hm.trans (matrixCompensatedState_spectral_tail F X hX hXh hXn hzero
    hs hs1 n (s*t-2*s^2*v))
  have he : -(s*t-2*s^2*v) = -s*t+2*s^2*v := by ring
  rw [he] at ht
  exact ht

#print axioms matrix_martingale_spectral_tail
end SpectralRadiusUpperTail
