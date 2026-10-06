import SpectralRadiusUpperTail.GaussianStoppedTruncationError
import SpectralRadiusUpperTail.GaussianUniformTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianTruncationTail (μ : Measure 𝕂) (d R : ℝ) : ℝ :=
  (16/d)*Real.exp (-(d/16)*R^2)*gaussianErrorExpBound μ d

lemma gaussianTruncationTail_nonneg (μ : Measure 𝕂) (d R : ℝ) (hd : 0 < d) :
    0 ≤ gaussianTruncationTail μ d R := by
  unfold gaussianTruncationTail gaussianErrorExpBound
  positivity

/-- The stopped discarded error has the uniform exponential conditional
second-moment bound under the actual terminal-row filtration. -/
theorem gaussianStoppedTruncationError_conditional_bound
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    ∀ᵐ x ∂gaussianSequentialRowLaw μ v a N t N,
      (gaussianSequentialRowLaw μ v a N t N)[
        (fun y => ‖gaussianStoppedTruncationError μ v a N t K R n y‖^2) | pathFiltration N n] x ≤
          gaussianTruncationTail μ d R := by
  have hh := (gaussianStoppedTruncationError_conditional_secondMoment μ hX hm v a ha N t n hn K R hR).2
  filter_upwards [hh] with x hx
  rw [hx]
  by_cases hs : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) K n
  · rw [Set.indicator_of_mem hs]
    exact (gaussianTruncatedSequentialIncrement_safe_bounds μ hX hm hvar v N hv a d ha hd
      hexp t n hn K δ R hK hδ hR hb hunit herror x hs).2
  · rw [Set.indicator_of_notMem hs]
    exact gaussianTruncationTail_nonneg μ d R hd

/-- Conditional integration gives the actual single-entry discarded second
moment, with all integrability established before the bound is integrated. -/
theorem gaussianStoppedTruncationError_secondMoment_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (t : 𝕂) (n : ℕ) (hn : n < N) (K δ R : ℝ) (hK : 0 ≤ K) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hb : ‖v (N-(n+1))‖ ≤ δ)
    (hunit : gaussianTruncationScale μ a d K*δ ≤ 1)
    (herror : (gaussianTruncationScale μ a d K*δ)*gaussianLocalMomentCost μ d ≤ 1/2) :
    Integrable (fun x => ‖gaussianStoppedTruncationError μ v a N t K R n x‖^2)
      (gaussianSequentialRowLaw μ v a N t N) ∧
      (∫ x, ‖gaussianStoppedTruncationError μ v a N t K R n x‖^2
        ∂gaussianSequentialRowLaw μ v a N t N) ≤ gaussianTruncationTail μ d R := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  refine ⟨(gaussianStoppedTruncationError_conditional_secondMoment μ hX hm v a ha N t n hn K R hR).1, ?_⟩
  have hh := gaussianStoppedTruncationError_conditional_bound μ hX hm hvar v N hv a d ha hd
    hexp t n hn K δ R hK hδ hR hb hunit herror
  calc
    _ = ∫ x, (gaussianSequentialRowLaw μ v a N t N)[
        (fun y => ‖gaussianStoppedTruncationError μ v a N t K R n y‖^2) | pathFiltration N n] x
        ∂gaussianSequentialRowLaw μ v a N t N := (integral_condExp ((pathFiltration N).le n)).symm
    _ ≤ ∫ _, gaussianTruncationTail μ d R ∂gaussianSequentialRowLaw μ v a N t N :=
      integral_mono_ae integrable_condExp (integrable_const _) hh
    _ = _ := by simp

#print axioms gaussianStoppedTruncationError_secondMoment_le
end SpectralRadiusUpperTail
