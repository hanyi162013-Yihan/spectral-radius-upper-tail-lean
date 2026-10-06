import SpectralRadiusUpperTail.RealArrayGaussianDensity
import SpectralRadiusUpperTail.RealPairSpectralGapIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- The actual unnormalized four-entry Gaussian measure restricted to
blocks with a nonreal conjugate pair. -/
noncomputable def realPairGaussianNonrealMeasure (n : ℝ) : Measure ((Fin 2 × Fin 2) → ℝ) :=
  (realArrayGaussianMeasure n).restrict realPairNonrealEntrySet

/-- Pushforward by the explicit spectral and gap coordinates. -/
noncomputable def realPairSpectralGapMeasure (n : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (realPairGaussianNonrealMeasure n).map realPairSpectralGapCoordinates

theorem realPairGaussianNonrealMeasure_finite (n : ℝ) (hn : 0 < n) :
    IsFiniteMeasure (realPairGaussianNonrealMeasure n) := by
  let := realArrayGaussianMeasure_finite (ι := Fin 2 × Fin 2) n hn
  unfold realPairGaussianNonrealMeasure
  infer_instance

theorem realPairSpectralGapMeasure_finite (n : ℝ) (hn : 0 < n) :
    IsFiniteMeasure (realPairSpectralGapMeasure n) := by
  let := realPairGaussianNonrealMeasure_finite n hn
  unfold realPairSpectralGapMeasure
  infer_instance

theorem realPairGaussianNonrealMeasure_lintegral
    (n : ℝ) (H : ((Fin 2 × Fin 2) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ A, H A ∂realPairGaussianNonrealMeasure n) =
      ∫⁻ A in realPairNonrealEntrySet, realPairGaussianWeight n A * H A := by
  unfold realPairGaussianNonrealMeasure realArrayGaussianMeasure
  rw [restrict_withDensity measurableSet_realPairNonrealEntrySet]
  exact lintegral_withDensity_eq_lintegral_mul _ (realPairGaussianWeight_measurable n) hH

/-- Exact scalar-coordinate law of the actual Gaussian block. -/
theorem realPairSpectralGapMeasure_lintegral
    (n : ℝ) (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v ∂realPairSpectralGapMeasure n) = ENNReal.ofReal (2*Real.pi) *
      (∫⁻ x : ℝ, ∫⁻ v in realSchurPairCoordinateDomain,
        ENNReal.ofReal (Real.exp (-n*(x^2+v.1))) *
          (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) *
            ENNReal.ofReal (Real.exp (-(n/2)*v.2)) * F (x,v))) := by
  rw [realPairSpectralGapMeasure,lintegral_map hF realPairSpectralGapCoordinates_measurable,
    realPairGaussianNonrealMeasure_lintegral n (fun A => F (realPairSpectralGapCoordinates A))
      (hF.comp realPairSpectralGapCoordinates_measurable)]
  exact realPairGaussian_spectralGap_lintegral n F hF

#print axioms realPairGaussianNonrealMeasure_finite
#print axioms realPairSpectralGapMeasure_finite
#print axioms realPairGaussianNonrealMeasure_lintegral
#print axioms realPairSpectralGapMeasure_lintegral
end SpectralRadiusUpperTail
