import SpectralRadiusUpperTail.RealGaussianSubstatIntegrable
import SpectralRadiusUpperTail.RealGaussianUpperHalfPlanePower
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set

/-- The weighted finite-dimensional one-point bounds and an actual
conditional-Schur comparison suffice for the Gaussian Hilbert--Schmidt
power input. Integrability of the root statistics is now proved from
Gaussian matrix moments, rather than assumed separately. -/
theorem gaussianPowerUpperInput_of_upper_half_weighted_onePoint_noInt
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
    (hSchur : GaussianSchurPowerComparisonInput) :
    GaussianPowerUpperInput := by
  exact gaussianPowerUpperInput_of_upper_half_weighted_onePoint
    (fun n k hn => realGaussianPositiveRealExteriorPower_integrable
      n k (by omega))
    (fun n k hn => realGaussianUpperNonrealExteriorPower_integrable
      n k (by omega))
    hPos hUpper hSchur

#print axioms gaussianPowerUpperInput_of_upper_half_weighted_onePoint_noInt
end SpectralRadiusUpperTail
