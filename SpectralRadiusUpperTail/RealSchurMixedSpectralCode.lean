import SpectralRadiusUpperTail.RealSchurMixedCanonicalSpectrum
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal
import SpectralRadiusUpperTail.MonicDivisorRootTests

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

/-- A finite code recording which canonical eigenvalue labels belong
to each ordered diagonal block. -/
noncomputable def realSchurMixedSpectralCode
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool := by
  classical
  exact fun a i => decide (
    (((realSchurMixedDiagonalMatrix s T a).charpoly.map Complex.ofRealHom).eval
      (realSchurMixedCanonicalSpectrum s T i))=0)

theorem realSchurMixedDiagonalMatrix_charpoly_dvd
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0) (a : Fin m) :
    (realSchurMixedDiagonalMatrix s T a).charpoly ∣ T.charpoly := by
  rw [realSchurMixed_blockUpper_charpoly s hs T hT]
  simp_rw [realSchurMixedDiagonalMatrix_charpoly]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ a)

/-- Equal codes for two block-upper matrices with the same simple
global spectrum force equal ordered diagonal-block characteristic
polynomials. The actual matrices inside the blocks may differ. -/
theorem realSchurMixed_diagonal_charpoly_eq_of_code
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0)
    (hU : realSchurMixedLowerProjection s U=0)
    (hsep : T.charpoly.Separable) (hpoly : T.charpoly=U.charpoly)
    (hcode : realSchurMixedSpectralCode s T=realSchurMixedSpectralCode s U)
    (a : Fin m) :
    (realSchurMixedDiagonalMatrix s T a).charpoly =
      (realSchurMixedDiagonalMatrix s U a).charpoly := by
  classical
  have hU_sep : U.charpoly.Separable := hpoly ▸ hsep
  have hlabels := realSchurMixedCanonicalSpectrum_eq_of_charpoly s T U hsep hU_sep hpoly
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  apply complexMonicDivisors_eq_of_label_tests (realSchurMixedCanonicalSpectrum s T)
    (T.charpoly.map Complex.ofRealHom)
  · exact (Polynomial.separable_map (algebraMap ℝ ℂ)).mpr hsep
  · exact (Matrix.charpoly_monic _).map _
  · exact (Matrix.charpoly_monic _).map _
  · exact Polynomial.map_dvd _ (realSchurMixedDiagonalMatrix_charpoly_dvd s hs T hT a)
  · rw [hpoly]
    exact Polynomial.map_dvd _ (realSchurMixedDiagonalMatrix_charpoly_dvd s hs U hU a)
  · exact realSchurMixedCanonicalSpectrum_covers s T hsep
  · intro i
    have hi := congrFun (congrFun hcode a) i
    simpa only [realSchurMixedSpectralCode, hlabels, decide_eq_decide] using hi

#print axioms realSchurMixedDiagonalMatrix_charpoly_dvd
#print axioms realSchurMixed_diagonal_charpoly_eq_of_code
end SpectralRadiusUpperTail
