import SpectralRadiusUpperTail.RealSchurMixedResultantFactor
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The lower-entry embedding has no diagonal or upper-block entries. -/
theorem realSchurMixedLowerEmbed_apply_upper
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (i j : RealSchurMixedCoord s) (hij : i.1 ≤ j.1) :
    realSchurMixedLowerEmbed s ω i j = 0 := by
  classical
  simp only [realSchurMixedLowerEmbed, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro q _
  have hne : ¬ (realSchurMixedLowerRow s q = i ∧
      realSchurMixedLowerCol s q = j) := by
    rintro ⟨hr,hc⟩
    have hq : (realSchurMixedLowerCol s q).1 <
        (realSchurMixedLowerRow s q).1 := q.1.2
    rw [hr,hc] at hq
    exact (not_lt_of_ge hij) hq
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, mul_zero]

/-- The fixed upper residual reads an original matrix entry unchanged
whenever the entry belongs to a diagonal or upper block. -/
theorem realSchurMixedUpperEntries_apply_upper
    {m : ℕ} (s : Fin m → ℕ)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (i j : RealSchurMixedCoord s) (hij : i.1 ≤ j.1) :
    (realSchurMixedUpperEntries s A).val i j = A i j := by
  change (A-realSchurMixedLowerEmbed s
    (realSchurMixedLowerProjection s A)) i j = A i j
  rw [Matrix.sub_apply,
    realSchurMixedLowerEmbed_apply_upper s _ i j hij, sub_zero]

/-- Under the complete fixed entry splitting, all diagonal and strict
upper coordinates are literally the original matrix entries. -/
theorem realSchurMixedFlatEntry_upper_coordinates
    {m : ℕ} (s : Fin m → ℕ)
    (f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ) :
    (realSchurMixedUpperEntryEquiv s
      (realSchurMixedEntryEquiv s
        ((realMatrixEntryEquiv (RealSchurMixedCoord s)).symm f)).2) =
      ((fun p : RealSchurMixedDiagonalEntry s => f p.val),
       (fun p : RealSchurMixedStrictUpperEntry s => f p.val)) := by
  apply Prod.ext <;> funext p
  · exact realSchurMixedUpperEntries_apply_upper s _ p.1.1 p.1.2
      (le_of_eq p.2)
  · exact realSchurMixedUpperEntries_apply_upper s _ p.1.1 p.1.2
      (le_of_lt p.2)

#print axioms realSchurMixedFlatEntry_upper_coordinates
end SpectralRadiusUpperTail
