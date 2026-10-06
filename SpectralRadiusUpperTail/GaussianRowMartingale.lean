import SpectralRadiusUpperTail.GaussianTerminalAdapted
import SpectralRadiusUpperTail.IncrementMartingale

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual cumulative centered error is a martingale on the terminal
Gaussian-soft coupled row, with its proved history filtration. -/
theorem gaussianTerminalRow_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) :
    Martingale (incrementPartialSum (gaussianTerminalIncrement μ v a N t))
      (pathFiltration N) (gaussianSequentialRowLaw μ v a N t N) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  exact martingale_incrementPartialSum _ _ _
    (gaussianTerminalIncrement_stronglyMeasurable_next μ hX v a ha N t)
    (fun n => (gaussianTerminalIncrement_condExp_zero μ hX hm v a ha N t n).1)
    (fun n => (gaussianTerminalIncrement_condExp_zero μ hX hm v a ha N t n).2)

#print axioms gaussianTerminalRow_martingale
end SpectralRadiusUpperTail
