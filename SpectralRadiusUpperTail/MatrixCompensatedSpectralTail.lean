import SpectralRadiusUpperTail.MatrixCompensatedTraceMarkov
import SpectralRadiusUpperTail.MatrixExponentialTraceSpectrum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Spectral upper tail for the actual compensated cumulative state. -/
theorem matrixCompensatedState_spectral_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) (u : ℝ) :
    μ.real {x | ∃ l ∈ spectrum ℝ (matrixCompensatedState μ F X s n x), u ≤ l} ≤
      (Fintype.card ι : ℝ) * Real.exp (-u) := by
  have hb := matrixCompensatedState_basics F X hX hXh hXn hs hs1 n
  have hsub : {x | ∃ l ∈ spectrum ℝ (matrixCompensatedState μ F X s n x), u ≤ l}
      ≤ᵐ[μ] {x | Real.exp u ≤ RCLike.re
        (NormedSpace.exp (matrixCompensatedState μ F X s n x)).trace} := by
    filter_upwards [hb.2.1] with x hx
    rintro ⟨l, hl, hu⟩
    rw [hx.spectrum_real_eq_range_eigenvalues] at hl
    obtain ⟨i, rfl⟩ := hl
    exact matrix_exp_threshold_le_trace hx ⟨i, hu⟩
  have hm := measure_mono_ae hsub
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hm
  exact hr.trans (matrixCompensatedState_trace_tail F X hX hXh hXn hzero hs hs1 n u)

#print axioms matrixCompensatedState_spectral_tail
end SpectralRadiusUpperTail
