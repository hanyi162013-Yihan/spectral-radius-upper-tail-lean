import SpectralRadiusUpperTail.RealSchurAtomicFlagSource
import SpectralRadiusUpperTail.RealSchurMixedSylvesterSpectralDependence
import SpectralRadiusUpperTail.RealSchurMixedFlagGaussianFactors

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

/-- The diagonal restriction of an atomic atlas chart depends only on
the ordered block characteristic polynomials. -/
theorem realSchurAtomicDiagonalSource_iff_of_polynomials
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (d e : RealSchurMixedDiagonalEntry s → ℝ)
    (hdiag : ∀ i, (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d 0) i).charpoly=
      (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s e 0) i).charpoly) :
    d ∈ realSchurAtomicDiagonalSource s code ↔ e ∈ realSchurAtomicDiagonalSource s code := by
  have hpoly := realSchurMixed_charpoly_eq_of_diagonal_polynomials s hs _ _
    (realSchurMixedUpperEntryJoin_lower_zero s d 0)
    (realSchurMixedUpperEntryJoin_lower_zero s e 0) hdiag
  by_cases hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable
  · have hsep' : (realSchurMixedUpperEntryJoin s e 0).charpoly.Separable := hpoly ▸ hsep
    have hcode := realSchurMixedSpectralCode_eq_of_diagonal_polynomials s hs _ _
      (realSchurMixedUpperEntryJoin_lower_zero s d 0)
      (realSchurMixedUpperEntryJoin_lower_zero s e 0) hsep hdiag
    have htest := realSchurAtomicCodeTest_iff_of_charpoly s code _ _ hsep hsep' hpoly
    change ((realSchurMixedUpperEntryJoin s d 0).charpoly.Separable ∧
      realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d 0)=code) ∧
        realSchurAtomicCodeTest s code (realSchurMixedUpperEntryJoin s d 0) ↔
      ((realSchurMixedUpperEntryJoin s e 0).charpoly.Separable ∧
      realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s e 0)=code) ∧
        realSchurAtomicCodeTest s code (realSchurMixedUpperEntryJoin s e 0)
    rw [hpoly,hcode,htest]
  · have hsep' : ¬(realSchurMixedUpperEntryJoin s e 0).charpoly.Separable := hpoly ▸ hsep
    simp [realSchurAtomicDiagonalSource,realSchurMixedDiagonalCodeSource,hsep,hsep']

/-- The spectral part of the full diagonal Jacobian excludes its
entrywise Gaussian energy. -/
noncomputable def realSchurMixedDiagonalGapWeight
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) : ℝ :=
  ∏ p : RealSchurLowerIndex m,
    |(realSchurMixedSylvester s (realSchurMixedUpperEntryJoin s d 0) p).det|

theorem realSchurMixedDiagonalGapWeight_eq_of_polynomials
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (d e : RealSchurMixedDiagonalEntry s → ℝ)
    (hdiag : ∀ i, (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d 0) i).charpoly=
      (realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s e 0) i).charpoly) :
    realSchurMixedDiagonalGapWeight s d=realSchurMixedDiagonalGapWeight s e := by
  apply Finset.prod_congr rfl
  intro p _
  rw [realSchurMixedSylvester_det_eq_of_diagonal_charpoly s hs _ _ hdiag p]

theorem realSchurMixedDiagonalGaussianJacobian_eq_gapWeight
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurMixedDiagonalGaussianJacobian s d =
      realSchurMixedDiagonalGapWeight s d *
        Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2) := rfl

#print axioms realSchurAtomicDiagonalSource_iff_of_polynomials
#print axioms realSchurMixedDiagonalGapWeight_eq_of_polynomials
#print axioms realSchurMixedDiagonalGaussianJacobian_eq_gapWeight
end SpectralRadiusUpperTail
