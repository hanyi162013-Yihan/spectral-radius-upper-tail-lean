import SpectralRadiusUpperTail.GaussianTerminalTruncationError

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianStoppedTruncationError (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (K R : ℝ) (n : ℕ) :
    (Fin N → 𝕂 × 𝕂) → 𝕂 :=
  gaussianStoppedIncrement μ v a N t K n-gaussianTruncatedStoppedIncrement μ v a N t K R n

lemma gaussianStoppedTruncationError_eq_indicator (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (K R : ℝ) (n : ℕ) :
    gaussianStoppedTruncationError μ v a N t K R n =
      (prefixSafeEvent (gaussianTerminalTarget v N t) K n).indicator
        (gaussianTerminalTruncationError μ v a N t R n) := by
  funext x
  by_cases hx : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n
  · simp only [gaussianStoppedTruncationError, Pi.sub_apply, gaussianStoppedIncrement,
      gaussianTruncatedStoppedIncrement, Set.indicator_of_mem hx, gaussianTerminalTruncationError]
  · simp only [gaussianStoppedTruncationError, Pi.sub_apply, gaussianStoppedIncrement,
      gaussianTruncatedStoppedIncrement, Set.indicator_of_notMem hx, sub_self]

lemma gaussianStoppedTruncationError_square_eq_indicator (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (K R : ℝ) (n : ℕ) :
    (fun x => ‖gaussianStoppedTruncationError μ v a N t K R n x‖^2) =
      (prefixSafeEvent (gaussianTerminalTarget v N t) K n).indicator
        (fun x => ‖gaussianTerminalTruncationError μ v a N t R n x‖^2) := by
  rw [gaussianStoppedTruncationError_eq_indicator, indicator_norm_sq_eq]

/-- Actual integrability and conditional moment of the stopped discarded
error. Its predictable safe indicator multiplies the actual kernel moment. -/
theorem gaussianStoppedTruncationError_conditional_secondMoment
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (K R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun x => ‖gaussianStoppedTruncationError μ v a N t K R n x‖^2)
      (gaussianSequentialRowLaw μ v a N t N) ∧
      (gaussianSequentialRowLaw μ v a N t N)[
        (fun x => ‖gaussianStoppedTruncationError μ v a N t K R n x‖^2) | pathFiltration N n] =ᵐ[
          gaussianSequentialRowLaw μ v a N t N]
      (prefixSafeEvent (gaussianTerminalTarget v N t) K n).indicator
        (fun x => ∫ p, ‖gaussianSequentialIncrement μ v a N t n (pathSuffix N n hn.le x,p)-
          gaussianTruncatedSequentialIncrement μ v a N t n R (pathSuffix N n hn.le x,p)‖^2
            ∂gaussianSequentialKernel μ v a N t n (pathSuffix N n hn.le x)) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  have hi := gaussianTerminalTruncationError_square_integrable μ hX hm v a ha N t n hn R hR
  have hA := prefixSafeEvent_measurable _ _ (gaussianTerminalTarget_measurable v N t) K n
  rw [gaussianStoppedTruncationError_square_eq_indicator]
  refine ⟨hi.indicator (((pathFiltration N).le n) _ hA), ?_⟩
  apply (condExp_indicator hi hA).trans
  have hh := gaussianTerminalTruncationError_conditional_secondMoment μ hX hm v a ha N t n hn R hR
  filter_upwards [hh] with x hx
  by_cases hxs : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n
  · simpa only [Set.indicator_of_mem hxs] using hx
  · simp only [Set.indicator_of_notMem hxs]

#print axioms gaussianStoppedTruncationError_conditional_secondMoment
end SpectralRadiusUpperTail
