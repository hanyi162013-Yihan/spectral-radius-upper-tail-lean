import SpectralRadiusUpperTail.GaussianTruncationErrorL2
import SpectralRadiusUpperTail.GaussianTerminalConditionalMean
import SpectralRadiusUpperTail.GaussianTerminalTruncation
import SpectralRadiusUpperTail.IndicatorSquare

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianTerminalTruncationError (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (R : ℝ) (n : ℕ) :
    (Fin N → 𝕂 × 𝕂) → 𝕂 :=
  gaussianTerminalIncrement μ v a N t n-gaussianTruncatedTerminalIncrement μ v a N t R n

lemma gaussianTerminalTruncationError_pullback (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (R : ℝ) (n : ℕ) (hn : n < N) :
    (fun x => ‖gaussianTerminalTruncationError μ v a N t R n x‖^2) =
      (fun z => ‖gaussianSequentialIncrement μ v a N t n z-
        gaussianTruncatedSequentialIncrement μ v a N t n R z‖^2) ∘ pathStep N n hn := by
  rw [gaussianTerminalTruncationError, gaussianTerminalIncrement_of_lt μ v a N t n hn,
    gaussianTruncatedTerminalIncrement, dif_pos hn]
  rfl

theorem gaussianTerminalTruncationError_square_integrable
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun x => ‖gaussianTerminalTruncationError μ v a N t R n x‖^2)
      (gaussianSequentialRowLaw μ v a N t N) := by
  rw [gaussianTerminalTruncationError_pullback μ v a N t R n hn]
  have hi := gaussianSequentialTruncationError_square_integrable μ hX hm v a ha N t n hn R hR
  rw [← gaussianSequentialRowLaw_step μ v a ha N t n hn] at hi
  exact hi.comp_measurable (pathStep_measurable N n hn)

/-- The actual terminal conditional squared truncation error is the actual
kernel error integral at the observed history. -/
theorem gaussianTerminalTruncationError_conditional_secondMoment
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂)
    (n : ℕ) (hn : n < N) (R : ℝ) (hR : 0 ≤ R) :
    (gaussianSequentialRowLaw μ v a N t N)[
      (fun x => ‖gaussianTerminalTruncationError μ v a N t R n x‖^2) | pathFiltration N n] =ᵐ[
        gaussianSequentialRowLaw μ v a N t N]
      fun x => ∫ p, ‖gaussianSequentialIncrement μ v a N t n (pathSuffix N n hn.le x,p)-
        gaussianTruncatedSequentialIncrement μ v a N t n R (pathSuffix N n hn.le x,p)‖^2
          ∂gaussianSequentialKernel μ v a N t n (pathSuffix N n hn.le x) := by
  rw [gaussianTerminalTruncationError_pullback μ v a N t R n hn]
  have hf := (gaussianSequentialIncrement_continuous μ hX v a ha N t n).measurable
  have ht := (gaussianTruncatedSequentialIncrement_basics μ hX v a ha N t n R hR).1
  exact gaussianTerminal_condExp_step μ v a ha N t n hn _
    ((hf.sub ht).norm.pow_const 2).stronglyMeasurable
    (gaussianSequentialTruncationError_square_integrable μ hX hm v a ha N t n hn R hR)

#print axioms gaussianTerminalTruncationError_conditional_secondMoment
end SpectralRadiusUpperTail
