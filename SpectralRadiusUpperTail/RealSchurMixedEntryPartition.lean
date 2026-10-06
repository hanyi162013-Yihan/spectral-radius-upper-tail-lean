import SpectralRadiusUpperTail.RealSchurMixedEntryEvaluation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Matrix entries outside the strictly lower blocks. -/
abbrev RealSchurMixedNonlowerEntry {m : ℕ} (s : Fin m → ℕ) :=
  {p : RealSchurMixedCoord s × RealSchurMixedCoord s //
    ¬ p.2.1 < p.1.1}

abbrev RealSchurMixedNonlowerDiagonalEntry
    {m : ℕ} (s : Fin m → ℕ) :=
  {p : RealSchurMixedNonlowerEntry s // p.1.1.1 = p.1.2.1}

abbrev RealSchurMixedNonlowerStrictEntry
    {m : ℕ} (s : Fin m → ℕ) :=
  {p : RealSchurMixedNonlowerEntry s // ¬ p.1.1.1 = p.1.2.1}

/-- Remove the redundant nonlower witness from a diagonal entry. -/
def realSchurMixedDiagonalPartitionEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedDiagonalEntry s ≃
      RealSchurMixedNonlowerDiagonalEntry s where
  toFun p := ⟨⟨p.val, not_lt_of_ge (le_of_eq p.property)⟩,p.property⟩
  invFun p := ⟨p.val.val,p.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨⟨p,h⟩,hd⟩; rfl

/-- Remove the redundant nonlower witness from a strict-upper entry. -/
def realSchurMixedStrictPartitionEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedStrictUpperEntry s ≃
      RealSchurMixedNonlowerStrictEntry s where
  toFun p := ⟨⟨p.val, not_lt_of_ge (le_of_lt p.property)⟩,
    ne_of_lt p.property⟩
  invFun p := ⟨p.val.val, by
    have hle : p.val.val.1.1 ≤ p.val.val.2.1 := le_of_not_gt p.val.property
    exact lt_of_le_of_ne hle p.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨⟨p,h⟩,hne⟩; rfl

#print axioms realSchurMixedDiagonalPartitionEquiv
#print axioms realSchurMixedStrictPartitionEquiv
end SpectralRadiusUpperTail
