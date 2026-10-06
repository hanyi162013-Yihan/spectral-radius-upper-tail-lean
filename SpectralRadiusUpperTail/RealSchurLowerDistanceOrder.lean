import SpectralRadiusUpperTail.RealSchurScalarOrbitDeterminant
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Lexicographic key for a lower block: distance, row, then column. -/
def realSchurLowerKey {m : ℕ} (p : RealSchurLowerIndex m) :
    Fin m ×ₗ (Fin m ×ₗ Fin m) :=
  toLex (realSchurLowerDistance p, toLex (p.1.1, p.1.2))

theorem realSchurLowerKey_injective {m : ℕ} :
    Function.Injective (realSchurLowerKey (m := m)) := by
  intro p q h
  have hpq : p.1 = q.1 :=
    congrArg (fun z : Fin m ×ₗ (Fin m ×ₗ Fin m) =>
      ofLex (ofLex z).2) h
  exact Subtype.ext hpq

/-- Lower-block coordinates ordered first by distance from the diagonal,
then lexicographically by their row and column. -/
noncomputable def realSchurLowerDistanceLinearOrder (m : ℕ) :
    LinearOrder (RealSchurLowerIndex m) :=
  LinearOrder.lift' realSchurLowerKey realSchurLowerKey_injective

/-- Strict order on lower blocks can only come from increasing distance or
from two distinct blocks at equal distance. -/
theorem realSchurLower_lt_cases {m : ℕ}
    (p q : RealSchurLowerIndex m)
    (h : realSchurLowerKey p < realSchurLowerKey q) :
    realSchurLowerDistance p < realSchurLowerDistance q ∨
      (realSchurLowerDistance p = realSchurLowerDistance q ∧ p ≠ q) := by
  unfold realSchurLowerKey at h
  rcases (Prod.Lex.toLex_lt_toLex).mp h with hdist | ⟨hdist, _⟩
  · exact Or.inl hdist
  · refine Or.inr ⟨hdist, ?_⟩
    intro heq
    subst q
    exact (lt_irrefl _) h

#print axioms realSchurLower_lt_cases
end SpectralRadiusUpperTail
