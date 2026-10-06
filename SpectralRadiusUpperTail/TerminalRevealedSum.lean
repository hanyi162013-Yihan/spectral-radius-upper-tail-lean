import SpectralRadiusUpperTail.FinitePathFiltration
import SpectralRadiusUpperTail.RevealedWeights

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
  [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]

/-- The actual revealed sum on the terminal path, constant after the horizon. -/
def terminalRevealedSum (f : ℕ → α → E) (N n : ℕ) : (Fin N → α) → E :=
  if h : n ≤ N then revealedSum f N n ∘ pathSuffix N n h else revealedSum f N N

lemma terminalRevealedSum_of_le (f : ℕ → α → E) (N n : ℕ) (h : n ≤ N) :
    terminalRevealedSum f N n = revealedSum f N n ∘ pathSuffix N n h := dif_pos h

lemma terminalRevealedSum_of_ge (f : ℕ → α → E) (N n : ℕ) (h : N ≤ n) :
    terminalRevealedSum f N n = revealedSum f N N := by
  by_cases hn : n ≤ N
  · have he : n=N := le_antisymm hn h
    subst n
    rw [terminalRevealedSum_of_le f N N le_rfl, pathSuffix_self, Function.comp_id]
  · exact dif_neg hn

/-- Every current sum uses only the coordinates already revealed. -/
lemma terminalRevealedSum_measurable (f : ℕ → α → E) (hf : ∀ n, Measurable (f n))
    (N n : ℕ) : Measurable[pathFiltration N n] (terminalRevealedSum f N n) := by
  by_cases hn : n ≤ N
  · rw [terminalRevealedSum_of_le f N n hn, pathFiltration_of_le N n hn]
    exact (revealedSum_measurable f hf N n).comp (comap_measurable _)
  · rw [terminalRevealedSum_of_ge f N n (by omega), pathFiltration_of_ge N n (by omega)]
    exact revealedSum_measurable f hf N N

lemma terminalRevealedSum_zero (f : ℕ → α → E) (N : ℕ) :
    terminalRevealedSum f N 0 = 0 := by
  rw [terminalRevealedSum_of_le f N 0 (Nat.zero_le _)]
  funext x
  simp [Function.comp_def, revealedSum]

#print axioms terminalRevealedSum_measurable
end SpectralRadiusUpperTail
