import SpectralRadiusUpperTail.FinitePathStep
import SpectralRadiusUpperTail.ConditionalMean
import Mathlib.Probability.Process.Filtration

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

/-- One filtration on the terminal path space, revealing suffix coordinates
in order and remaining constant after the terminal horizon. -/
def pathFiltration (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Fin N → α)) where
  seq n := if h : n ≤ N then MeasurableSpace.comap (pathSuffix N n h) inferInstance
    else inferInstance
  mono' := by
    intro i j hij
    by_cases hj : j ≤ N
    · have hi := hij.trans hj
      simp only [dif_pos hi, dif_pos hj]
      exact MeasurableSpace.comap_le_comap_of_eq_comp _
        (pathSuffix_measurable j i hij) (pathSuffix_comp N j i hj hij).symm
    · simp only [dif_neg hj]
      split_ifs with hi
      · exact (pathSuffix_measurable N i hi).comap_le
      · exact le_rfl
  le' n := by
    split_ifs with hn
    · exact (pathSuffix_measurable N n hn).comap_le
    · exact le_rfl

lemma pathFiltration_of_le (N n : ℕ) (h : n ≤ N) :
    pathFiltration (α := α) N n =
      MeasurableSpace.comap (pathSuffix N n h) inferInstance := by
  change (if h : n ≤ N then _ else _) = _
  rw [dif_pos h]

lemma pathFiltration_of_ge (N n : ℕ) (h : N ≤ n) :
    pathFiltration (α := α) N n = (inferInstance : MeasurableSpace (Fin N → α)) := by
  by_cases hn : n ≤ N
  · have he : n=N := le_antisymm hn h
    subst n
    rw [pathFiltration_of_le N N le_rfl, pathSuffix_self, MeasurableSpace.comap_id]
  · change (if h : n ≤ N then _ else _) = _
    rw [dif_neg hn]

lemma pathStep_historySigma (N n : ℕ) (h : n < N) :
    MeasurableSpace.comap (pathStep (α := α) N n h) historySigma =
      pathFiltration N n := by
  rw [pathFiltration_of_le N n h.le]
  unfold historySigma
  rw [MeasurableSpace.comap_comp]
  rfl

/-- The actual next-step projection is measurable at the next history time. -/
lemma pathStep_measurable_next (N n : ℕ) (h : n < N) :
    Measurable[pathFiltration (α := α) N (n+1)] (pathStep N n h) := by
  rw [pathFiltration_of_le N (n+1) (by omega), pathStep_eq_uncons_suffix]
  exact (pathUncons_measurable n).comp (comap_measurable _)

#print axioms pathFiltration
#print axioms pathStep_measurable_next
end SpectralRadiusUpperTail
