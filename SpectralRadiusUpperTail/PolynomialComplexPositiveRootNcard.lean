import SpectralRadiusUpperTail.PolynomialComplexRealRootFilter
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- At simple spectrum, the complex-root counting convention used by the
matrix radius event equals the cardinality of the marked positive real
root fiber. -/
theorem realPolynomial_complexPositiveRealCount_eq_ncard
    (p : ℝ[X]) (hp : p ≠ 0) (hsep : p.Separable) (t : ℝ) :
    Multiset.countP (fun z : ℂ => z.im = 0 ∧ t < z.re) (p.aroots ℂ) =
      Set.ncard {x : ℝ | p.IsRoot x ∧ t < x} := by
  rw [realPolynomial_complexPositiveRealCount_eq_realCount]
  exact polynomial_simpleRealRoot_countP_eq_ncard p hp hsep (fun x => t < x)

#print axioms realPolynomial_complexPositiveRealCount_eq_ncard
end SpectralRadiusUpperTail
