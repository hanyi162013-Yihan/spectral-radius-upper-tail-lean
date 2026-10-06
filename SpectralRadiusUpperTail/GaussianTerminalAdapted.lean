import SpectralRadiusUpperTail.GaussianTerminalIncrement
import SpectralRadiusUpperTail.GaussianIncrementContinuity
import Mathlib.Probability.Process.Adapted

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual terminal increment is measurable when its new coordinate has
been revealed, including the zero continuation after the horizon. -/
theorem gaussianTerminalIncrement_measurable_next (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) :
    Measurable[pathFiltration N (n+1)] (gaussianTerminalIncrement μ v a N t n) := by
  by_cases hn : n < N
  · have hh := (gaussianSequentialIncrement_continuous μ hX v a ha N t n).measurable.comp
      (pathStep_measurable_next N n hn)
    rw [gaussianTerminalIncrement_of_lt μ v a N t n hn]
    exact hh
  · rw [gaussianTerminalIncrement_of_ge μ v a N t n (Nat.le_of_not_gt hn)]
    exact measurable_const

lemma gaussianTerminalIncrement_stronglyMeasurable_next (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) :
    StronglyMeasurable[pathFiltration N (n+1)] (gaussianTerminalIncrement μ v a N t n) :=
  (gaussianTerminalIncrement_measurable_next μ hX v a ha N t n).stronglyMeasurable

#print axioms gaussianTerminalIncrement_stronglyMeasurable_next
end SpectralRadiusUpperTail
