import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Complex characteristic roots of every actual mixed-Schur chart
parameter are the multiset sum of the complex roots of its current
diagonal blocks, with algebraic multiplicities retained. -/
theorem realSchurMixedExpCoordinates_aroots
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (x : RealSchurMixedTangent s) :
    (realSchurMixedExpCoordinates s T x).charpoly.aroots ℂ =
      (Finset.univ : Finset (Fin m)).val.bind
        (fun i => ((T+x.2.val).toSquareBlock
          (fun z : RealSchurMixedCoord s => z.1) i).charpoly.aroots ℂ) := by
  rw [realSchurMixedExpCoordinates_charpoly s hs T hT x]
  simp only [Polynomial.aroots_def, Polynomial.map_prod]
  apply Polynomial.roots_prod
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Polynomial.map_monic_ne_zero
    (Matrix.charpoly_monic
      ((T+x.2.val).toSquareBlock
        (fun z : RealSchurMixedCoord s => z.1) i))

#print axioms realSchurMixedExpCoordinates_aroots
end SpectralRadiusUpperTail
