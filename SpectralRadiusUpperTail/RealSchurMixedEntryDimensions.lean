import SpectralRadiusUpperTail.RealSchurMixedEntryPartition
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Transposition identifies a lower-block entry with a strictly-upper
block entry; these are the same number of real coordinates. -/
def realSchurMixedLowerStrictUpperEquiv
    {m : ℕ} (s : Fin m → ℕ) :
    RealSchurMixedLowerEntry s ≃ RealSchurMixedStrictUpperEntry s where
  toFun p := ⟨(p.val.2,p.val.1),p.property⟩
  invFun p := ⟨(p.val.2,p.val.1),p.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The angular coordinate count matches the number of independent
strictly-upper block entries. -/
theorem realSchurMixedOrbit_card_eq_strictUpper_card
    {m : ℕ} (s : Fin m → ℕ) :
    Fintype.card (RealSchurMixedOrbitIndex s) =
      Fintype.card (RealSchurMixedStrictUpperEntry s) := by
  exact Fintype.card_congr
    ((realSchurMixedLowerEntryEquiv s).trans
      (realSchurMixedLowerStrictUpperEquiv s))

#print axioms realSchurMixedOrbit_card_eq_strictUpper_card
end SpectralRadiusUpperTail
