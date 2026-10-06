import SpectralRadiusUpperTail.GaussianTerminalLaw
import SpectralRadiusUpperTail.FinitePathFiltration
import SpectralRadiusUpperTail.ConditionalPullback
import SpectralRadiusUpperTail.GaussianIncrementHistory

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The actual centered increment as a function on one terminal paired-row
space. It is zero after the finite horizon. -/
noncomputable def gaussianTerminalIncrement (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (x : Fin N → 𝕂 × 𝕂) : 𝕂 :=
  if h : n < N then gaussianSequentialIncrement μ v a N t n (pathStep N n h x) else 0

lemma gaussianTerminalIncrement_of_lt (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (h : n < N) :
    gaussianTerminalIncrement μ v a N t n =
      gaussianSequentialIncrement μ v a N t n ∘ pathStep N n h := by
  funext x
  exact dif_pos h

lemma gaussianTerminalIncrement_of_ge (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (h : N ≤ n) :
    gaussianTerminalIncrement μ v a N t n = 0 := by
  funext x
  exact dif_neg (Nat.not_lt.mpr h)

/-- The actual terminal increment is integrable and conditionally centered
with respect to the filtration on the single terminal probability space. -/
theorem gaussianTerminalIncrement_condExp_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) :
    Integrable (gaussianTerminalIncrement μ v a N t n) (gaussianSequentialRowLaw μ v a N t N) ∧
      (gaussianSequentialRowLaw μ v a N t N)[gaussianTerminalIncrement μ v a N t n |
        pathFiltration N n] =ᵐ[gaussianSequentialRowLaw μ v a N t N] 0 := by
  have (k : ℕ) : IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t k) :=
    gaussianSequentialRowLaw_probability μ v a ha N t k
  have (k : ℕ) : IsMarkovKernel (gaussianSequentialKernel μ v a N t k) :=
    gaussianSequentialKernel_markov μ v a ha N t k
  by_cases hn : n < N
  · have hc := gaussianSequentialIncrement_condExp_zero μ hX hm v a ha N t n hn
    have hp := condExp_pullback_eq_zero (gaussianSequentialRowLaw μ v a N t N)
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n)
      (pathStep N n hn) (pathStep_measurable N n hn)
      (gaussianSequentialRowLaw_step μ v a ha N t n hn) historySigma historySigma_le
      (gaussianSequentialIncrement μ v a N t n) hc.1 hc.2
    rw [gaussianTerminalIncrement_of_lt μ v a N t n hn]
    simpa only [pathStep_historySigma] using hp
  · rw [gaussianTerminalIncrement_of_ge μ v a N t n (Nat.le_of_not_gt hn)]
    simp

lemma pathStep_upperPairedHistory (N : ℕ) (j : Fin N) (x : Fin N → 𝕂 × 𝕂) :
    pathStep N (N-(j.val+1)) (by omega) x = (upperPairedHistory j x,x j) := by
  apply Prod.ext
  · funext i
    dsimp only [pathStep, pathSuffix, upperPairedHistory]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · dsimp only [pathStep]
    congr 1
    apply Fin.ext
    dsimp
    omega

/-- The terminal increment is the same actual centered error that appears in
the full triangular matrix equality. -/
theorem gaussianTerminalIncrement_at_coordinate (μ : Measure 𝕂) (v : ℕ → 𝕂)
    (a : ℝ) (N : ℕ) (t : 𝕂) (j : Fin N) (x : Fin N → 𝕂 × 𝕂) :
    gaussianTerminalIncrement μ v a N t (N-(j.val+1)) x =
      gaussianRowCenteredIncrement μ a v j t (coordinateVector Prod.fst N x)
        (comparatorVector N x) := by
  rw [gaussianTerminalIncrement, dif_pos (by omega), pathStep_upperPairedHistory]
  exact gaussianSequentialIncrement_eq_row_increment μ v a t j x

#print axioms gaussianTerminalIncrement_condExp_zero
#print axioms gaussianTerminalIncrement_at_coordinate
end SpectralRadiusUpperTail
