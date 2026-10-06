import SpectralRadiusUpperTail.GaussianTerminalTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- All individual stopped-row difference properties, including square
integrability, for transport to the full matrix probability space. -/
theorem gaussianTruncatedStoppedIncrement_basics (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (K R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    Integrable (gaussianTruncatedStoppedIncrement μ v a N t K R n)
        (gaussianSequentialRowLaw μ v a N t N) ∧
      (gaussianSequentialRowLaw μ v a N t N)[gaussianTruncatedStoppedIncrement μ v a N t K R n |
        pathFiltration N n] =ᵐ[gaussianSequentialRowLaw μ v a N t N] 0 ∧
      Measurable[pathFiltration N (n+1)] (gaussianTruncatedStoppedIncrement μ v a N t K R n) ∧
      Integrable (fun x => ‖gaussianTruncatedStoppedIncrement μ v a N t K R n x‖^2)
        (gaussianSequentialRowLaw μ v a N t N) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  have hb := gaussianTruncatedTerminalIncrement_basics μ hX v a ha N t R hR
  have hA := prefixSafeEvent_measurable _ _ (gaussianTerminalTarget_measurable v N t) K
  have hp := predictableIndicator_condExp_zero (gaussianSequentialRowLaw μ v a N t N)
    (pathFiltration N) _ _ hA (fun k => (hb k).1) (fun k => (hb k).2.1) n
  have hd : Measurable[pathFiltration N (n+1)]
      (gaussianTruncatedStoppedIncrement μ v a N t K R n) :=
    (hb n).2.2.1.indicator (((pathFiltration N).mono (Nat.le_succ n)) _ (hA n))
  refine ⟨hp.1, hp.2, hd, ?_⟩
  have hm := ((hd.mono ((pathFiltration N).le (n+1)) le_rfl).norm.pow_const 2)
  apply (integrable_const ((2*R)^2)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)).mpr
    (gaussianTruncatedStoppedIncrement_norm_le μ hX v a ha N t K R hR n x)
  simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hs

#print axioms gaussianTruncatedStoppedIncrement_basics
end SpectralRadiusUpperTail
