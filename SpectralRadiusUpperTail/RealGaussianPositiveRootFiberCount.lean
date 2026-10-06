import SpectralRadiusUpperTail.RealGaussianPositiveRootPredicateScale
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- On simple-spectrum matrices, the actual normalized positive-real
root count is exactly the cardinality of the unscaled marked-root fiber
above `r√n`. This links the geometric incidence space to the existing
spectral-radius count statistic. -/
theorem realGaussianExteriorCount_positive_eq_rootFiberNcard
    (n : ℕ) (hn : 0 < n) (r : ℝ)
    (a : (Fin n × Fin n) → ℝ)
    (hsep : (Matrix.of a.curry).charpoly.Separable) :
    realGaussianExteriorCount n r 0 a =
      (Set.ncard {x : ℝ |
        (Matrix.of a.curry).charpoly.IsRoot x ∧
          r * Real.sqrt (n : ℝ) < x} : ℝ) := by
  classical
  rw [realGaussianExteriorCount_eq_unscaled_countP n hn r 0 a]
  let p := (Matrix.of a.curry).charpoly
  have hcount :
      Multiset.countP
        (fun z : ℂ => realGaussianExteriorPredicate r 0
          ((((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * z)) (p.aroots ℂ) =
        Multiset.countP
          (fun z : ℂ => z.im = 0 ∧ r * Real.sqrt (n : ℝ) < z.re)
          (p.aroots ℂ) := by
    apply Multiset.countP_congr rfl
    intro z _
    exact propext (realGaussian_positiveRootPredicate_unscale n hn r z)
  rw [hcount]
  exact_mod_cast realPolynomial_complexPositiveRealCount_eq_ncard p
    (Matrix.of a.curry).charpoly_monic.ne_zero hsep
    (r * Real.sqrt (n : ℝ))

#print axioms realGaussianExteriorCount_positive_eq_rootFiberNcard
end SpectralRadiusUpperTail
