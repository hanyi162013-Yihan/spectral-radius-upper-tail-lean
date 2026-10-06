import SpectralRadiusUpperTail.MarkedRealDiagonalCharpolyFactor
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- A simple complementary spectrum, with the marked scalar avoiding its
roots, gives a simple full two-block spectrum. -/
theorem markedRealDiagonal_product_separable
    (m : ℕ) (x : ℝ) (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H.charpoly.Separable)
    (hx : H.charpoly.eval x ≠ 0) :
    ((Polynomial.X - Polynomial.C x) * H.charpoly).Separable := by
  have hnot : ¬ (Polynomial.X - Polynomial.C x) ∣ H.charpoly := by
    intro hdvd
    exact hx ((Polynomial.dvd_iff_isRoot).mp hdvd)
  have hcop : IsCoprime (Polynomial.X - Polynomial.C x) H.charpoly :=
    (Polynomial.irreducible_X_sub_C x).coprime_iff_not_dvd.mpr hnot
  exact Polynomial.separable_X_sub_C.mul hH hcop

#print axioms markedRealDiagonal_product_separable
end SpectralRadiusUpperTail
