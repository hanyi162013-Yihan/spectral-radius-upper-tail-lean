import SpectralRadiusUpperTail.RealSchurMixedChartRootCounts
import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Every point of a rotated regular mixed-Schur chart has complex
roots exactly supplied by its current diagonal blocks, with multiplicity. -/
theorem realSchurMixed_rotatedExpCoordinates_aroots_countP
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hQ : Qᵀ*Q=1)
    (x : RealSchurMixedTangent s)
    (p : ℂ → Prop) [DecidablePred p] :
    Multiset.countP p
      ((Q*(realSchurMixedExpCoordinates s T x)*Qᵀ).charpoly.aroots ℂ) =
      ∑ i : Fin m, Multiset.countP p
        (((T+x.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i).charpoly.aroots ℂ) := by
  rw [realMatrixOrthogonalConjugation_charpoly _ Q _ hQ]
  exact realSchurMixedExpCoordinates_aroots_countP s hs T hT x p

#print axioms realSchurMixed_rotatedExpCoordinates_aroots_countP
end SpectralRadiusUpperTail
