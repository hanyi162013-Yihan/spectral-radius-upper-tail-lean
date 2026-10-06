import SpectralRadiusUpperTail.RealGaussianRealIntensity
import SpectralRadiusUpperTail.GaussianMarkedRealScaledWeight
import SpectralRadiusUpperTail.RealGaussianPositiveCountUnscaled
import SpectralRadiusUpperTail.PositiveScalarTailLIntegral
import SpectralRadiusUpperTail.MeasureEqualityFromOpenTails

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Equality of the actual real-eigenvalue intensity measure with its
explicit Gaussian density. All real cutoffs are used, so this also
supports arbitrary nonnegative measurable spectral weights. -/
theorem realGaussianRealIntensity_eq_density (m : ℕ) (hm : 0 < m) :
    realGaussianRealIntensity (m+1) =
      volume.withDensity (gaussianMarkedRealScaledWeight m) := by
  apply realMeasure_eq_of_open_tails
  intro b
  rw [realGaussianRealIntensity_open_tail (m+1) (by omega) b,
    realGaussian_positiveCount_unscaled m hm b,
    withDensity_apply _ measurableSet_Ioi,
    mul_comm b, positiveScalar_tail_lintegral _ b (by positivity)]
  rfl

theorem realGaussianRealIntensity_lintegral_density
    (m : ℕ) (hm : 0 < m) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, w x ∂realGaussianRealIntensity (m+1)) =
      ∫⁻ x, gaussianMarkedRealScaledWeight m x * w x := by
  rw [realGaussianRealIntensity_eq_density m hm,
    lintegral_withDensity_eq_lintegral_mul _
      (gaussianMarkedRealScaledWeight_measurable m) hw]
  rfl

#print axioms realGaussianRealIntensity_eq_density
#print axioms realGaussianRealIntensity_lintegral_density
end SpectralRadiusUpperTail
