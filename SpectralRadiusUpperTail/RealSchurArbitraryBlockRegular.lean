import SpectralRadiusUpperTail.RealSchurSylvesterKernel
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Simple spectrum makes the flag Jacobian regular for arbitrary
positive block sizes, including one marked pair and a large complement. -/
theorem realSchurMixed_simpleSpectrum_orbit_regular_general
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0)
    (hsep : T.charpoly.Separable) :
    (realSchurMixedOrbitMatrix s T).det ≠ 0 := by
  have htri := (realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hT
  have hupper : ∀ a b : Fin m, b < a →
      ∀ x : Fin (s a), ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩=0 := by
    intro a b hab x y
    exact htri hab
  have hpair := realSchurMixed_blockUpper_charpoly_pairwise_coprime s hs T hT hsep
  rw [realSchurMixedOrbitMatrix_det s hs T hupper]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [realSchurMixedSylvester_eq_diagonalMatrix]
  apply realSchurRectangularSylvester_ne_zero_of_coprime
  have h := @hpair p.1.1 p.1.2 (ne_of_gt p.2)
  simpa only [realSchurMixedDiagonalMatrix_charpoly] using h

#print axioms realSchurMixed_simpleSpectrum_orbit_regular_general
end SpectralRadiusUpperTail
