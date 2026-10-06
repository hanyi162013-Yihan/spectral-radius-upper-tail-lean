import SpectralRadiusUpperTail.RealSchurMixedBlockCharpoly
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators
open Polynomial

/-- A separable product has pairwise coprime distinct factors. -/
theorem realPolynomial_pairwise_coprime_of_separable_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ[X])
    (hsep : (∏ i, p i).Separable) :
    Pairwise (fun i j => IsCoprime (p i) (p j)) := by
  intro i j hij
  have hj : j ≠ i := Ne.symm hij
  have hsubset : ({i, j} : Finset ι) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hdiv : p i * p j ∣ ∏ k, p k := by
    have h := Finset.prod_dvd_prod_of_subset ({i, j} : Finset ι)
      Finset.univ p hsubset
    simpa [hij, hj] using h
  exact (hsep.of_dvd hdiv).isCoprime

/-- Under a separable characteristic polynomial, all diagonal-block
characteristic polynomials of a block-upper matrix are pairwise coprime. -/
theorem realSchurMixed_blockUpper_charpoly_pairwise_coprime
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hsep : T.charpoly.Separable) :
    Pairwise (fun i j : Fin m =>
      IsCoprime
        (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) i).charpoly
        (T.toSquareBlock (fun z : RealSchurMixedCoord s => z.1) j).charpoly) := by
  rw [realSchurMixed_blockUpper_charpoly s hs T hT] at hsep
  exact realPolynomial_pairwise_coprime_of_separable_prod _ hsep

#print axioms realSchurMixed_blockUpper_charpoly_pairwise_coprime
end SpectralRadiusUpperTail
