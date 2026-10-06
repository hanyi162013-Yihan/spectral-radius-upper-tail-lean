import SpectralRadiusUpperTail.RealSchurMixedSeparatedBlocks
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators
open Polynomial

/-- Any two disjoint collections of diagonal-block characteristic
polynomials in a simple-spectrum block-upper matrix are coprime. In
particular this applies to a prefix and its trailing quotient. -/
theorem realSchurMixed_disjointBlockProducts_coprime
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hsep : T.charpoly.Separable)
    (I J : Finset (Fin m)) (hdis : Disjoint I J) :
    IsCoprime
      (∏ i ∈ I,
        (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) i).charpoly)
      (∏ j ∈ J,
        (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) j).charpoly) := by
  have hpair := realSchurMixed_blockUpper_charpoly_pairwise_coprime
    s hs T hT hsep
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  have hij : i ≠ j := by
    intro e
    subst j
    exact (Finset.disjoint_left.mp hdis hi hj)
  exact hpair hij

#print axioms realSchurMixed_disjointBlockProducts_coprime
end SpectralRadiusUpperTail
