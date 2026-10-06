import SpectralRadiusUpperTail.MarkedRealAngularGaussianMomentFormula
import SpectralRadiusUpperTail.RealSchurMixedEntryDimensions
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The free upper row in a two-block real-Schur matrix has exactly
m Gaussian coordinates. -/
theorem markedRealTwoBlock_strictUpper_card (m : ℕ) :
    Fintype.card
      (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)) = m := by
  calc
    Fintype.card
        (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m)) =
      Fintype.card
        (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m)) :=
      (realSchurMixedOrbit_card_eq_strictUpper_card
        (markedRealTwoBlockSizes m)).symm
    _ = m := by
      simpa using (Fintype.card_congr (markedRealOrbitEquiv m)).symm

#print axioms markedRealTwoBlock_strictUpper_card
end SpectralRadiusUpperTail
