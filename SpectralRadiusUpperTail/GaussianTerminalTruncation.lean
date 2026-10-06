import SpectralRadiusUpperTail.GaussianKernelTruncation
import SpectralRadiusUpperTail.GaussianStoppedRow

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual conditionally recentered truncation on one terminal row space. -/
noncomputable def gaussianTruncatedTerminalIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (R : ℝ) (n : ℕ) :
    (Fin N → 𝕂 × 𝕂) → 𝕂 :=
  if h : n < N then gaussianTruncatedSequentialIncrement μ v a N t n R ∘ pathStep N n h else 0

/-- All martingale-difference properties and the deterministic increment bound
hold under the actual terminal row law, including the zero continuation. -/
theorem gaussianTruncatedTerminalIncrement_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    Integrable (gaussianTruncatedTerminalIncrement μ v a N t R n)
        (gaussianSequentialRowLaw μ v a N t N) ∧
      (gaussianSequentialRowLaw μ v a N t N)[gaussianTruncatedTerminalIncrement μ v a N t R n |
        pathFiltration N n] =ᵐ[gaussianSequentialRowLaw μ v a N t N] 0 ∧
      Measurable[pathFiltration N (n+1)] (gaussianTruncatedTerminalIncrement μ v a N t R n) ∧
      ∀ x, ‖gaussianTruncatedTerminalIncrement μ v a N t R n x‖ ≤ 2*R := by
  have (k : ℕ) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t k) :=
    gaussianSequentialRowLaw_probability μ v a ha N t k
  have (k : ℕ) : IsMarkovKernel (gaussianSequentialKernel μ v a N t k) :=
    gaussianSequentialKernel_markov μ v a ha N t k
  by_cases hn : n < N
  · rw [gaussianTruncatedTerminalIncrement, dif_pos hn]
    have hb := gaussianTruncatedSequentialIncrement_basics μ hX v a ha N t n R hR
    have hp := condExp_pullback_eq_zero (gaussianSequentialRowLaw μ v a N t N)
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)
      (pathStep N n hn) (pathStep_measurable N n hn)
      (gaussianSequentialRowLaw_step μ v a ha N t n hn) historySigma historySigma_le
      (gaussianTruncatedSequentialIncrement μ v a N t n R) hb.2.1 hb.2.2.1
    rw [pathStep_historySigma] at hp
    exact ⟨hp.1, hp.2, hb.1.comp (pathStep_measurable_next N n hn),
      fun x => hb.2.2.2 (pathStep N n hn x)⟩
  · rw [gaussianTruncatedTerminalIncrement, dif_neg hn]
    refine ⟨integrable_zero _ _ _, ?_, measurable_const, ?_⟩
    · simp
    · intro x
      simpa only [Pi.zero_apply, norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR

/-- The actual bounded truncated row differences sum to a martingale. -/
theorem gaussianTruncatedRow_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (R : ℝ) (hR : 0 ≤ R) :
    Martingale (incrementPartialSum (gaussianTruncatedTerminalIncrement μ v a N t R))
      (pathFiltration N) (gaussianSequentialRowLaw μ v a N t N) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  have hb := gaussianTruncatedTerminalIncrement_basics μ hX v a ha N t R hR
  exact martingale_incrementPartialSum _ _ _ (fun n => (hb n).2.2.1.stronglyMeasurable)
    (fun n => (hb n).1) (fun n => (hb n).2.1)

noncomputable def gaussianTruncatedStoppedIncrement (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (K R : ℝ) (n : ℕ) :
    (Fin N → 𝕂 × 𝕂) → 𝕂 :=
  (prefixSafeEvent (gaussianTerminalTarget v N t) K n).indicator
    (gaussianTruncatedTerminalIncrement μ v a N t R n)

/-- Actual predictable prefix stopping and actual conditional recentering
produce the bounded row martingale needed by the later matrix construction. -/
theorem gaussianTruncatedStoppedRow_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (K R : ℝ) (hR : 0 ≤ R) :
    Martingale (incrementPartialSum (gaussianTruncatedStoppedIncrement μ v a N t K R))
      (pathFiltration N) (gaussianSequentialRowLaw μ v a N t N) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  have hb := gaussianTruncatedTerminalIncrement_basics μ hX v a ha N t R hR
  exact martingale_predictableIndicator _ _ _ _
    (prefixSafeEvent_measurable _ _ (gaussianTerminalTarget_measurable v N t) K)
    (fun n => (hb n).2.2.1.stronglyMeasurable) (fun n => (hb n).1) (fun n => (hb n).2.1)

lemma gaussianTruncatedStoppedIncrement_norm_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (K R : ℝ) (hR : 0 ≤ R) (n : ℕ) (x : Fin N → 𝕂 × 𝕂) :
    ‖gaussianTruncatedStoppedIncrement μ v a N t K R n x‖ ≤ 2*R := by
  unfold gaussianTruncatedStoppedIncrement
  by_cases hx : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n
  · rw [Set.indicator_of_mem hx]
    exact (gaussianTruncatedTerminalIncrement_basics μ hX v a ha N t R hR n).2.2.2 x
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

#print axioms gaussianTruncatedStoppedRow_martingale
#print axioms gaussianTruncatedStoppedIncrement_norm_le
end SpectralRadiusUpperTail
