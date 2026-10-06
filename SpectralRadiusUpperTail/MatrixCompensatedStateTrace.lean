import SpectralRadiusUpperTail.MatrixCompensatedState

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
variable {𝕂 : Type*} [RCLike 𝕂] {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] matrixL2RealNormedAlgebra

/-- Adaptedness and bounded Hermitian structure of the constructed state. -/
theorem matrixCompensatedState_basics {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2)
    (n : ℕ) :
    StronglyMeasurable[F n] (matrixCompensatedState μ F X s n) ∧
    (∀ᵐ x ∂μ, (matrixCompensatedState μ F X s n x).IsHermitian) ∧
    (∀ᵐ x ∂μ, ‖matrixCompensatedState μ F X s n x‖ ≤ (n : ℝ)) := by
  induction n with
  | zero =>
    simp only [matrixCompensatedState, Finset.range_zero, Finset.sum_empty]
    exact ⟨stronglyMeasurable_const, Filter.Eventually.of_forall (fun _ => Matrix.isHermitian_zero),
      Filter.Eventually.of_forall (fun _ => by simp)⟩
  | succ n ih =>
    have hb := matrixCompensatedIncrement_basics F X n (hX n) (hXh n) (hXn n) hs hs1
    have he : matrixCompensatedState μ F X s (n+1) = fun x =>
        matrixCompensatedState μ F X s n x + matrixCompensatedIncrement μ F X s n x :=
      funext (matrixCompensatedState_succ μ F X s n)
    rw [he]
    refine ⟨(ih.1.mono (F.mono (Nat.le_succ n))).add hb.1, ?_, ?_⟩
    · filter_upwards [ih.2.1, hb.2.1] with x hx hy
      exact hx.add hy
    · filter_upwards [ih.2.2, hb.2.2] with x hx hy
      exact (norm_add_le _ _).trans (by simpa only [Nat.cast_add, Nat.cast_one] using add_le_add hx hy)

/-- Algebraic identification with the sum of increments and predictable squares. -/
lemma matrixCompensatedState_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F : Filtration ℕ mΩ) (X : ℕ → Ω → Matrix ι ι 𝕂)
    (s : ℝ) (n : ℕ) (x : Ω) : matrixCompensatedState μ F X s n x =
      s • (∑ i ∈ Finset.range n, X i x) -
        (2*s^2) • (∑ i ∈ Finset.range n, μ[fun y => (X i y)^2 | F i] x) := by
  simp only [matrixCompensatedState, matrixCompensatedIncrement,
    Finset.sum_sub_distrib, Finset.smul_sum]

/-- The finite sum has trace-exponential expectation at most the dimension.
All structural state hypotheses are proved here from the increments. -/
theorem matrixCompensatedState_trace_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] [Nonempty ι] (F : Filtration ℕ mΩ)
    (X : ℕ → Ω → Matrix ι ι 𝕂)
    (hX : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hXh : ∀ n, ∀ᵐ x ∂μ, (X n x).IsHermitian)
    (hXn : ∀ n, ∀ᵐ x ∂μ, ‖X n x‖ ≤ 1)
    (hzero : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (n : ℕ) :
    (∫ x, RCLike.re (NormedSpace.exp (matrixCompensatedState μ F X s n x)).trace ∂μ)
      ≤ Fintype.card ι := by
  have hb := matrixCompensatedState_basics F X hX hXh hXn hs hs1
  apply matrix_compensated_trace_iteration F (matrixCompensatedState μ F X s) X
    (fun j => (j : ℝ)) (fun j => (hb j).1) (fun j => (hb j).2.1)
    (fun j => (hb j).2.2) (fun j => ((hX j).mono (F.le (j+1))).aestronglyMeasurable)
    hXh hXn hzero (matrixCompensatedState_zero μ F X s) hs hs1
  intro j
  exact Filter.Eventually.of_forall (matrixCompensatedState_succ μ F X s j)

#print axioms matrixCompensatedState_basics
#print axioms matrixCompensatedState_trace_le
end SpectralRadiusUpperTail
