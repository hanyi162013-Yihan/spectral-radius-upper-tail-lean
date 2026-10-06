import SpectralRadiusUpperTail.GaussianRowMartingale
import SpectralRadiusUpperTail.TerminalRevealedSum
import SpectralRadiusUpperTail.PrefixSafeEvent

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

def gaussianTerminalTarget (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂) (n : ℕ)
    (x : Fin N → 𝕂 × 𝕂) : 𝕂 :=
  t-terminalRevealedSum (fun i p => v i*p.1) N n x

lemma gaussianTerminalTarget_measurable (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂) (n : ℕ) :
    Measurable[pathFiltration N n] (gaussianTerminalTarget v N t n) :=
  measurable_const.sub (terminalRevealedSum_measurable _
    (fun _ => measurable_const.mul measurable_fst) N n)

noncomputable def gaussianStoppedIncrement (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (R : ℝ) (n : ℕ) : (Fin N → 𝕂 × 𝕂) → 𝕂 :=
  (prefixSafeEvent (gaussianTerminalTarget v N t) R n).indicator
    (gaussianTerminalIncrement μ v a N t n)

/-- Actual predictable prefix stopping preserves the terminal-row martingale. -/
theorem gaussianStoppedRow_martingale (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (R : ℝ) :
    Martingale (incrementPartialSum (gaussianStoppedIncrement μ v a N t R))
      (pathFiltration N) (gaussianSequentialRowLaw μ v a N t N) := by
  have : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t N) :=
    gaussianSequentialRowLaw_probability μ v a ha N t N
  exact martingale_predictableIndicator _ _ _ _
    (prefixSafeEvent_measurable _ _ (gaussianTerminalTarget_measurable v N t) R)
    (gaussianTerminalIncrement_stronglyMeasurable_next μ hX v a ha N t)
    (fun n => (gaussianTerminalIncrement_condExp_zero μ hX hm v a ha N t n).1)
    (fun n => (gaussianTerminalIncrement_condExp_zero μ hX hm v a ha N t n).2)

/-- On the event of no bad prefix through n, the stopped and original sums agree. -/
lemma gaussianStoppedRow_eq_on_safe (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (R : ℝ) (n : ℕ) {x : Fin N → 𝕂 × 𝕂}
    (hx : x ∈ prefixSafeEvent (gaussianTerminalTarget v N t) R n) :
    incrementPartialSum (gaussianStoppedIncrement μ v a N t R) n x =
      incrementPartialSum (gaussianTerminalIncrement μ v a N t) n x := by
  apply Finset.sum_congr rfl
  intro k hk
  exact prefixSafeEvent_indicator_eq _ _ _ n k (Finset.mem_range.mp hk).le hx

#print axioms gaussianStoppedRow_martingale
#print axioms gaussianStoppedRow_eq_on_safe
end SpectralRadiusUpperTail
