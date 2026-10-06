import SpectralRadiusUpperTail.GaussianTerminalVariance

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual stopped, conditionally recentered terminal increment has a
conditional second moment proportional to its current coefficient, relative
to the actual terminal-row filtration. The unsafe histories contribute zero. -/
theorem gaussianTruncatedStoppedIncrement_conditional_variance_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    ∀ᵐ x ∂gaussianSequentialRowLaw μ v a N t N,
      (gaussianSequentialRowLaw μ v a N t N)[
        (fun y => ‖gaussianTruncatedStoppedIncrement μ v a N t K R n y‖^2) | pathFiltration N n] x ≤
          (12*gaussianTruncationScale μ a d K*gaussianLocalMomentCost μ d)*‖v (N-(n+1))‖ := by
  have hh := gaussianTruncatedStoppedIncrement_conditional_secondMoment μ hX v a ha N t K R hR n hn
  filter_upwards [hh] with x hx
  rw [hx]
  by_cases hxA : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n
  · rw [Set.indicator_of_mem hxA]
    exact (gaussianTruncatedSequentialIncrement_safe_bounds μ hX hm hvar v N hv a d ha hd
      hexp t n hn K δ R hK hδ hR hb hunit herror x hxA).1
  · rw [Set.indicator_of_notMem hxA]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (gaussianTruncationScale_nonneg μ a d K ha hd hK))
      (gaussianLocalMomentCost_nonneg μ d hd.le)) (norm_nonneg _)

#print axioms gaussianTruncatedStoppedIncrement_conditional_variance_le
end SpectralRadiusUpperTail
