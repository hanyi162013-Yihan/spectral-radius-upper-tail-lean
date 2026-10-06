import SpectralRadiusUpperTail.RealGaussianPositiveRootFiberCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The expected positive-real exterior count of the actual Gaussian
matrix is the expected cardinality of its marked-root fiber. This is the
precise target of the remaining global marked-line Kac--Rice formula. -/
theorem realGaussian_positiveCount_eq_rootFiberExpectation
    (n : ℕ) (hn : 0 < n) (r : ℝ) :
    (∫ a : (Fin n × Fin n) → ℝ,
      realGaussianExteriorCount n r 0 a ∂gaussianMatrixLaw n) =
      ∫ a : (Fin n × Fin n) → ℝ,
        (Set.ncard {x : ℝ |
          (Matrix.of a.curry).charpoly.IsRoot x ∧
            r * Real.sqrt (n : ℝ) < x} : ℝ)
        ∂gaussianMatrixLaw n := by
  apply integral_congr_ae
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with a ha
  exact realGaussianExteriorCount_positive_eq_rootFiberNcard n hn r a ha

#print axioms realGaussian_positiveCount_eq_rootFiberExpectation
end SpectralRadiusUpperTail
