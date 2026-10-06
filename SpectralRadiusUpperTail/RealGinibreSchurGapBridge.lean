import SpectralRadiusUpperTail.SchurGapNormalizerIntegral
import SpectralRadiusUpperTail.RealGinibreNonrealDensityAt
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The candidate nonreal one-point density contains precisely the local
real-Schur squared-gap integral, including its Gaussian and angular factors.
The actual Gaussian-matrix one-point identity remains a separate theorem. -/
theorem realGinibreNonrealDensityAt_eq_schurGapIntegral
    (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z.im ≠ 0) :
    realGinibreNonrealDensityAt n z =
      (n : ℝ)/Real.pi *
        ((n : ℝ)*|z.im| *
          (∫ s : ℝ in Ioi 0,
            Real.exp (-((n : ℝ)/2)*s) *
              (Real.sqrt (s+4*|z.im|^2))⁻¹)) *
        (Real.exp (-(n : ℝ)*‖z‖^2) *
          ginibreExpPartial (n-1) ((n : ℝ)*‖z‖^2)) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hy : 0 < |z.im| := abs_pos.mpr hz
  rw [realGinibreNonrealDensityAt, realGinibreNonrealDensity]
  rw [← schur_gap_integral_eq_erfc_correction (n : ℝ) |z.im| hnreal hy]

/-- The normalized positive squared-gap model has an explicit erfc density.
This remains a product-model law until a global real-Schur change of
variables identifies it with the Gaussian matrix. -/
theorem schurGapExplicitDensity_eq_erfc
    (n y s : ℝ) (hn : 0 < n) (hy : 0 < y) (hs : 0 ≤ s) :
    schurGapExplicitDensity n y s =
      ENNReal.ofReal ((n/2)*Real.exp (-(n/2)*s)) *
        (ENNReal.ofReal ((Real.sqrt (s+4*y^2))⁻¹) /
          ENNReal.ofReal
            (gaussianErfcCorrection (Real.sqrt (2*n)*y)/(2*y))) := by
  rw [schurGapExplicitDensity_of_pos n y s hn hy hs,
    schurGapKernelNormalizer_eq_erfcCorrection n y hn hy]

#print axioms realGinibreNonrealDensityAt_eq_schurGapIntegral
#print axioms schurGapExplicitDensity_eq_erfc
end SpectralRadiusUpperTail
