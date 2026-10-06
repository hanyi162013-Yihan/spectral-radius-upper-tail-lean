import SpectralRadiusUpperTail.RealGaussianPowerNonrealBoundary
import SpectralRadiusUpperTail.RealGaussianSchurPowerComparison

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The actual conditional Schur comparison is now proved. The only
remaining actual-distribution input in this Gaussian power route is the
upper-half-plane nonreal weighted one-point bound. -/
theorem gaussianPowerUpperInput_of_nonreal_weighted
    (hUpper : ∀ n k, 3 ≤ n →
      2*(∫ a, realGaussianUpperNonrealExteriorPower n k a ∂gaussianMatrixLaw n) ≤
        (∫ z : ℂ in {z | 1 < ‖z‖}, ‖z‖^(2*k)*realGinibreNonrealDensityAt n z)) :
    GaussianPowerUpperInput :=
  gaussianPowerUpperInput_of_nonreal_weighted_and_schur hUpper realGaussian_schur_power_comparison

#print axioms gaussianPowerUpperInput_of_nonreal_weighted
end SpectralRadiusUpperTail
