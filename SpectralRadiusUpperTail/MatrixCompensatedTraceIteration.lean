import SpectralRadiusUpperTail.MatrixCompensatedTraceIntegral
import Mathlib.Probability.Process.Filtration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
  [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Finite-horizon trace iteration from actual conditional centering and
conditional-square updates. No trace estimate or tail bound is assumed. -/
theorem matrix_compensated_trace_iteration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (S X : ℕ → Ω → Matrix ι ι 𝕂) (C : ℕ → ℝ)
    (hS : ∀ n, StronglyMeasurable[F n] (S n))
    (hSh : ∀ n, ∀ᵐ x ∂μ, (S n x).IsHermitian)
    (hSn : ∀ n, ∀ᵐ x ∂μ, ‖S n x‖ ≤ C n)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (hinit : ∀ x, S 0 x = 0) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2)
    (hrec : ∀ n, ∀ᵐ x ∂μ, S (n+1) x = S n x+
      (s • X n x-(2*s^2) • μ[fun y => (X n y)^2 | F n] x)) (n : ℕ) :
    (∫ x, RCLike.re (NormedSpace.exp (S n x)).trace ∂μ) ≤ Fintype.card ι := by
  induction n with
  | zero => simp [hinit,Matrix.trace_one]
  | succ n ih =>
    have he : (∫ x, RCLike.re (NormedSpace.exp (S (n+1) x)).trace ∂μ) =
        ∫ x, RCLike.re (NormedSpace.exp (S n x+
          (s • X n x-(2*s^2) • μ[fun y => (X n y)^2 | F n] x))).trace ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrec n] with x hx
      rw [hx]
    rw [he]
    exact (matrix_compensated_trace_integral_le (F.le n) (hS n) (hSh n) (C n)
      (hSn n) (hX n) (hXh n) (hXn n) (hzero n) hs hs1).trans ih

#print axioms matrix_compensated_trace_iteration
end SpectralRadiusUpperTail
