import SpectralRadiusUpperTail.RealGaussianRadiusFromWeightedOnePoint
import SpectralRadiusUpperTail.RealGaussianUpperHalfPlanePower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Set
open scoped Topology

/-- The Gaussian radius right-tail upper bound reduces to two weighted
one-point formulas: positive real roots and upper-half-plane nonreal roots.
Sign and conjugation symmetry account for the other two classes. The
finite-dimensional formulas remain explicit assumptions. -/
theorem realGaussianRadius_upper_of_two_weighted_classes
    (hPosInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianPositiveRealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hUpperInt : ∀ n k, 3 ≤ n →
      Integrable (realGaussianUpperNonrealExteriorPower n k)
        (gaussianMatrixLaw n))
    (hPos : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianPositiveRealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreFirstDensity n x) +
        (∫ x in Ioi (1 : ℝ),
          x^(2*k)*realGinibreDominantDensity n x))
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ x, realGaussianUpperNonrealExteriorPower n k x
        ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖},
          ‖z‖^(2*k)*realGinibreNonrealDensityAt n z))
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianMatrixLaw n).real
        {x | r ≤ realMatrixRadius
          ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) := by
  have hinput : ∀ n k, 3 ≤ n →
      Integrable (realGaussianExteriorRootPower n k) (gaussianMatrixLaw n) ∧
      (∫ x, realGaussianExteriorRootPower n k x
        ∂gaussianMatrixLaw n) ≤
          realGinibreWeightedOnePointEnvelope n k := by
    intro n k hn
    apply realGaussianExteriorRootPower_onePoint_transfer n k
      (hPosInt n k hn)
      (realGaussianNegativeRealExteriorPower_integrable n k (hPosInt n k hn))
      (realGaussianNonrealExteriorPower_integrable_of_upper n k (hUpperInt n k hn))
      (hPos n k hn)
    · rw [realGaussianWeightedRealHalflines_equal n k (hPosInt n k hn)]
      exact hPos n k hn
    · rw [realGaussianNonrealExteriorPower_mean_eq_two_upper]
      exact hUpper n k hn
  exact realGaussianRadius_upper_of_weightedOnePoint
    (fun n k hn => (hinput n k hn).1)
    (fun n k hn => (hinput n k hn).2)
    r hr ε hε

#print axioms realGaussianRadius_upper_of_two_weighted_classes
end SpectralRadiusUpperTail
