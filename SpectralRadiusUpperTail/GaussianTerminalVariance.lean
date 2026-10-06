import SpectralRadiusUpperTail.GaussianTerminalConditionalMean
import SpectralRadiusUpperTail.GaussianTerminalTruncation
import SpectralRadiusUpperTail.GaussianUniformTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual terminal conditional second moment equals the actual truncated
kernel second moment at the observed history. -/
theorem gaussianTruncatedTerminalIncrement_conditional_secondMoment
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : n < N) :
    (gaussianSequentialRowLaw μ v a N t N)[
      (fun x => ‖gaussianTruncatedTerminalIncrement μ v a N t R n x‖^2) | pathFiltration N n] =ᵐ[
        gaussianSequentialRowLaw μ v a N t N]
      fun x => ∫ p, ‖gaussianTruncatedSequentialIncrement μ v a N t n R
        (pathSuffix N n hn.le x,p)‖^2
          ∂gaussianSequentialKernel μ v a N t n (pathSuffix N n hn.le x) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
    gaussianSequentialRowLaw_probability μ v a ha N t n
  have : IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
    gaussianSequentialKernel_markov μ v a ha N t n
  have hb := gaussianTruncatedSequentialIncrement_basics μ hX v a ha N t n R hR
  let f := fun z => ‖gaussianTruncatedSequentialIncrement μ v a N t n R z‖^2
  have hfm : Measurable f := hb.1.norm.pow_const 2
  have hi : Integrable f ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) := by
    apply (integrable_const ((2*R)^2)).mono' hfm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)).mpr (hb.2.2.2 z)
    simpa only [f, Real.norm_eq_abs, abs_pow, abs_norm] using hs
  have hh := gaussianTerminal_condExp_step μ v a ha N t n hn f hfm.stronglyMeasurable hi
  have he : (fun x => ‖gaussianTruncatedTerminalIncrement μ v a N t R n x‖^2) =
      f ∘ pathStep N n hn := by
    rw [gaussianTruncatedTerminalIncrement, dif_pos hn]
    rfl
  rw [he]
  exact hh

/-- Stopping multiplies the actual conditional second moment by the same
predictable safe-history indicator. -/
theorem gaussianTruncatedStoppedIncrement_conditional_secondMoment
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (K R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : n < N) :
    (gaussianSequentialRowLaw μ v a N t N)[
      (fun x => ‖gaussianTruncatedStoppedIncrement μ v a N t K R n x‖^2) | pathFiltration N n] =ᵐ[
        gaussianSequentialRowLaw μ v a N t N]
      (prefixSafeEvent (gaussianTerminalTarget v N t) K n).indicator
        (fun x => ∫ p, ‖gaussianTruncatedSequentialIncrement μ v a N t n R
          (pathSuffix N n hn.le x,p)‖^2
            ∂gaussianSequentialKernel μ v a N t n (pathSuffix N n hn.le x)) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  let A := prefixSafeEvent (gaussianTerminalTarget v N t) K n
  let f := fun x => ‖gaussianTruncatedTerminalIncrement μ v a N t R n x‖^2
  have hb := gaussianTruncatedTerminalIncrement_basics μ hX v a ha N t R hR n
  have hfm : Measurable f := ((hb.2.2.1.mono ((pathFiltration N).le (n+1)) le_rfl).norm.pow_const 2)
  have hi : Integrable f (gaussianSequentialRowLaw μ v a N t N) := by
    apply (integrable_const ((2*R)^2)).mono' hfm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)).mpr (hb.2.2.2 x)
    simpa only [f, Real.norm_eq_abs, abs_pow, abs_norm] using hs
  have he : (fun x => ‖gaussianTruncatedStoppedIncrement μ v a N t K R n x‖^2) =
      A.indicator f := by
    funext x
    change ‖A.indicator (gaussianTruncatedTerminalIncrement μ v a N t R n) x‖^2 = A.indicator f x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
      norm_num
  rw [he]
  have ha' : MeasurableSet[pathFiltration N n] A :=
    prefixSafeEvent_measurable _ _ (gaussianTerminalTarget_measurable v N t) K n
  apply (condExp_indicator hi ha').trans
  have hh := gaussianTruncatedTerminalIncrement_conditional_secondMoment μ hX v a ha N t R hR n hn
  filter_upwards [hh] with x hx
  change A.indicator _ x = A.indicator _ x
  by_cases hxA : x ∈ A
  · simpa only [Set.indicator_of_mem hxA] using hx
  · simp only [Set.indicator_of_notMem hxA]

#print axioms gaussianTruncatedStoppedIncrement_conditional_secondMoment
end SpectralRadiusUpperTail
