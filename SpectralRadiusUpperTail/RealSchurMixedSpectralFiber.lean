import SpectralRadiusUpperTail.RealSchurMixedSpectralCode
import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator BigOperators

theorem realSchurMixed_charpoly_eq_of_diagonal_polynomials
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0)
    (hU : realSchurMixedLowerProjection s U=0)
    (hdiag : ∀ a, (realSchurMixedDiagonalMatrix s T a).charpoly =
      (realSchurMixedDiagonalMatrix s U a).charpoly) : T.charpoly=U.charpoly := by
  rw [realSchurMixed_blockUpper_charpoly s hs T hT,
    realSchurMixed_blockUpper_charpoly s hs U hU]
  simp_rw [realSchurMixedDiagonalMatrix_charpoly, hdiag]

theorem realSchurMixedSpectralCode_eq_of_diagonal_polynomials
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0)
    (hU : realSchurMixedLowerProjection s U=0)
    (hsep : T.charpoly.Separable)
    (hdiag : ∀ a, (realSchurMixedDiagonalMatrix s T a).charpoly =
      (realSchurMixedDiagonalMatrix s U a).charpoly) :
    realSchurMixedSpectralCode s T=realSchurMixedSpectralCode s U := by
  have hpoly := realSchurMixed_charpoly_eq_of_diagonal_polynomials s hs T U hT hU hdiag
  have hU_sep : U.charpoly.Separable := hpoly ▸ hsep
  have hlabels := realSchurMixedCanonicalSpectrum_eq_of_charpoly s T U hsep hU_sep hpoly
  funext a i
  simp only [realSchurMixedSpectralCode, hdiag, hlabels]

theorem realSchurMixedUpperEntryJoin_diagonalMatrix
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ) (a : Fin m) :
    realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d u) a =
      realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d v) a := by
  ext i j
  simp [realSchurMixedDiagonalMatrix, realSchurMixedUpperEntryJoin]

theorem realSchurMixedUpperEntryJoin_charpoly_fiber_const
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ) :
    (realSchurMixedUpperEntryJoin s d u).charpoly =
      (realSchurMixedUpperEntryJoin s d v).charpoly := by
  exact realSchurMixed_charpoly_eq_of_diagonal_polynomials s hs _ _
    (realSchurMixedUpperEntryJoin_lower_zero s d u)
    (realSchurMixedUpperEntryJoin_lower_zero s d v)
    (fun a => congrArg Matrix.charpoly (realSchurMixedUpperEntryJoin_diagonalMatrix s d u v a))

theorem realSchurMixedSpectralCode_fiber_const
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ)
    (hsep : (realSchurMixedUpperEntryJoin s d u).charpoly.Separable) :
    realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d u) =
      realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d v) := by
  exact realSchurMixedSpectralCode_eq_of_diagonal_polynomials s hs _ _
    (realSchurMixedUpperEntryJoin_lower_zero s d u)
    (realSchurMixedUpperEntryJoin_lower_zero s d v) hsep
    (fun a => congrArg Matrix.charpoly (realSchurMixedUpperEntryJoin_diagonalMatrix s d u v a))

#print axioms realSchurMixed_charpoly_eq_of_diagonal_polynomials
#print axioms realSchurMixedSpectralCode_eq_of_diagonal_polynomials
#print axioms realSchurMixedUpperEntryJoin_diagonalMatrix
#print axioms realSchurMixedUpperEntryJoin_charpoly_fiber_const
#print axioms realSchurMixedSpectralCode_fiber_const
end SpectralRadiusUpperTail
