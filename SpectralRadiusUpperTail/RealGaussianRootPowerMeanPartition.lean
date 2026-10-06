import SpectralRadiusUpperTail.RealGaussianSubstatIntegrable
import SpectralRadiusUpperTail.RealGaussianUpperHalfPlanePower

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- Gaussian sign symmetry and conjugate pairing reduce the entire
exterior root-power expectation to the positive real and upper nonreal
parts. Integrability of every term is supplied by Gaussian moments. -/
theorem realGaussianExteriorRootPower_mean_partition
    (n k : ℕ) (hn : 0 < n) :
    (∫ a, realGaussianExteriorRootPower n k a ∂gaussianMatrixLaw n) =
      2*(∫ a, realGaussianPositiveRealExteriorPower n k a ∂gaussianMatrixLaw n) +
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) := by
  have hp := realGaussianPositiveRealExteriorPower_integrable n k hn
  have hnint := realGaussianNegativeRealExteriorPower_integrable n k hp
  have hc := realGaussianNonrealExteriorPower_integrable_of_upper n k
    (realGaussianUpperNonrealExteriorPower_integrable n k hn)
  have heq : realGaussianExteriorRootPower n k =
      (fun a => realGaussianPositiveRealExteriorPower n k a +
        realGaussianNegativeRealExteriorPower n k a +
        realGaussianNonrealExteriorPower n k a) :=
    funext (realGaussianExteriorRootPower_partition n k)
  rw [heq]
  change (∫ a, ((realGaussianPositiveRealExteriorPower n k +
    realGaussianNegativeRealExteriorPower n k) +
    realGaussianNonrealExteriorPower n k) a ∂gaussianMatrixLaw n) = _
  rw [integral_add' (hp.add hnint) hc, integral_add' hp hnint,
    realGaussianWeightedRealHalflines_equal n k hp,
    realGaussianNonrealExteriorPower_mean_eq_two_upper]
  ring

#print axioms realGaussianExteriorRootPower_mean_partition
end SpectralRadiusUpperTail
