import SpectralRadiusUpperTail.RealGaussianNonrealWeightedUpper
import SpectralRadiusUpperTail.RealGaussianPowerLinearNonrealBoundary

namespace SpectralRadiusUpperTail

/-- The real Gaussian Hilbert--Schmidt power upper asymptotic follows from
the proved Schur comparison and the calibrated nonreal root bound. -/
theorem realGaussian_power_upper_proved : GaussianPowerUpperInput :=
  gaussianPowerUpperInput_of_linear_nonreal_weighted
    realGaussianNonrealWeightConstant realGaussianNonrealWeightConstant_pos
    realGaussianNonreal_weighted_linear_upper

#print axioms realGaussian_power_upper_proved
end SpectralRadiusUpperTail
