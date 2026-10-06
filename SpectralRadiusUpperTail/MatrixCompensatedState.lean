import SpectralRadiusUpperTail.MatrixCompensatedTraceIteration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- The actual conditional-square compensated increment. -/
noncomputable def matrixCompensatedIncrement {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℕ mΩ) (X : ℕ → Ω → Matrix ι ι 𝕂)
    (s : ℝ) (n : ℕ) (x : Ω) : Matrix ι ι 𝕂 :=
  s • X n x - (2*s^2) • μ[fun y => (X n y)^2 | F n] x

/-- Cumulative state with the actual conditional expectations. -/
noncomputable def matrixCompensatedState {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℕ mΩ) (X : ℕ → Ω → Matrix ι ι 𝕂)
    (s : ℝ) (n : ℕ) (x : Ω) : Matrix ι ι 𝕂 :=
  ∑ i ∈ Finset.range n, matrixCompensatedIncrement μ F X s i x

lemma matrixCompensatedState_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℕ mΩ) (X : ℕ → Ω → Matrix ι ι 𝕂)
    (s : ℝ) (x : Ω) : matrixCompensatedState μ F X s 0 x = 0 := by
  simp [matrixCompensatedState]

lemma matrixCompensatedState_succ {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℕ mΩ) (X : ℕ → Ω → Matrix ι ι 𝕂)
    (s : ℝ) (n : ℕ) (x : Ω) : matrixCompensatedState μ F X s (n+1) x =
      matrixCompensatedState μ F X s n x + matrixCompensatedIncrement μ F X s n x := by
  simp only [matrixCompensatedState, Finset.sum_range_succ]

lemma matrixCompensatedIncrement_basics {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂) (n : ℕ)
    (hX : StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) :
    StronglyMeasurable[F (n+1)] (matrixCompensatedIncrement μ F X s n) ∧
    (∀ᵐ x ∂μ, (matrixCompensatedIncrement μ F X s n x).IsHermitian) ∧
    (∀ᵐ x ∂μ, ‖matrixCompensatedIncrement μ F X s n x‖ ≤ 1) := by
  have hm := F.le n
  have hXm : AEStronglyMeasurable (X n) μ :=
    (hX.mono (F.le (n+1))).aestronglyMeasurable
  have h2n : ∀ᵐ x ∂μ, ‖(X n x)^2‖ ≤ 1 := by
    filter_upwards [hXn] with x hx
    have hh := norm_mul_le (X n x) (X n x)
    rw [← pow_two] at hh
    exact hh.trans (by nlinarith [norm_nonneg (X n x)])
  have hi2 := Integrable.of_bound (hXm.pow 2) 1 h2n
  have hD := matrix_conditional_square_contraction hm hi2 hXh hXn
  have hDm : StronglyMeasurable[F n] (μ[fun y => (X n y)^2 | F n]) :=
    stronglyMeasurable_condExp
  refine ⟨(hX.const_smul s).sub ((hDm.mono (F.mono (Nat.le_succ n))).const_smul (2*s^2)), ?_, ?_⟩
  · filter_upwards [hXh, hD] with x hx hd
    exact (hx.smul (show IsSelfAdjoint s from rfl)).sub
      (hd.1.isHermitian.smul (show IsSelfAdjoint (2*s^2) from rfl))
  · filter_upwards [hXn, hD] with x hx hd
    exact compensated_increment_norm_le_one s (X n x) _ hs hs1 hx hd.2

#print axioms matrixCompensatedIncrement_basics
end SpectralRadiusUpperTail
