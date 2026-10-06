import SpectralRadiusUpperTail.MatrixCompensatedStateTrace

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Markov bound for the actual compensated trace exponential. -/
theorem matrixCompensatedState_trace_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) (u : ℝ) :
    μ.real {x | Real.exp u ≤ RCLike.re
      (NormedSpace.exp (matrixCompensatedState μ F X s n x)).trace} ≤
        (Fintype.card ι : ℝ) * Real.exp (-u) := by
  have hb := matrixCompensatedState_basics F X hX hXh hXn hs hs1 n
  have hi := algebra_exp_integrable_of_bound
    (hb.1.mono (F.le n)).aestronglyMeasurable (n : ℝ) hb.2.2
  have hit : Integrable (fun x => RCLike.re
      (NormedSpace.exp (matrixCompensatedState μ F X s n x)).trace) μ :=
    (matrixRealTrace : Matrix ι ι 𝕂 →L[ℝ] ℝ).integrable_comp hi
  have hn : 0 ≤ᵐ[μ] (fun x => RCLike.re
      (NormedSpace.exp (matrixCompensatedState μ F X s n x)).trace) := by
    filter_upwards [hb.2.1] with x hx
    exact (RCLike.nonneg_iff.mp (matrix_exp_posSemidef hx).trace_nonneg).1
  have hm := (mul_meas_ge_le_integral_of_nonneg hn hit (Real.exp u)).trans
    (matrixCompensatedState_trace_le F X hX hXh hXn hzero hs hs1 n)
  rw [mul_comm] at hm
  have hd := (le_div_iff₀ (Real.exp_pos u)).2 hm
  simpa only [div_eq_mul_inv, Real.exp_neg] using hd

#print axioms matrixCompensatedState_trace_tail
end SpectralRadiusUpperTail
