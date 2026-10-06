import SpectralRadiusUpperTail.RealSchurSmallSylvesterCoprime
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- A separable characteristic polynomial makes the angular Jacobian
of every 1×1/2×2 block-upper representation nonsingular. This connects
the global Schur construction to the previously proved regular charts. -/
theorem realSchurMixed_simpleSpectrum_orbit_det_ne_zero
    {m : ℕ} (s : Fin m → ℕ)
    (hs : ∀ i, s i = 1 ∨ s i = 2)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hsep : T.charpoly.Separable) :
    (realSchurMixedOrbitMatrix s T).det ≠ 0 := by
  have hspos : ∀ i, 0 < s i := by
    intro i
    rcases hs i with h | h <;> omega
  have htri : T.BlockTriangular
      (fun z : RealSchurMixedCoord s => z.1) :=
    (realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hT
  have hupper : ∀ a b : Fin m, b < a →
      ∀ x : Fin (s a), ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0 := by
    intro a b h x y
    exact htri h
  have hpair := realSchurMixed_blockUpper_charpoly_pairwise_coprime
    s hspos T hT hsep
  rw [realSchurMixedOrbitMatrix_det s hspos T hupper]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [realSchurMixedSylvester_eq_diagonalMatrix]
  have hcop : IsCoprime
      (realSchurMixedDiagonalMatrix s T p.1.1).charpoly
      (realSchurMixedDiagonalMatrix s T p.1.2).charpoly := by
    have h := @hpair p.1.1 p.1.2 (ne_of_gt p.2)
    simpa only [realSchurMixedDiagonalMatrix_charpoly] using h
  exact realSchurRectangularSylvester_ne_zero_of_coprime_small
    (hs p.1.1) (hs p.1.2)
    (realSchurMixedDiagonalMatrix s T p.1.1)
    (realSchurMixedDiagonalMatrix s T p.1.2) hcop

#print axioms realSchurMixed_simpleSpectrum_orbit_det_ne_zero
end SpectralRadiusUpperTail
