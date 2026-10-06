import SpectralRadiusUpperTail.RealPairSpectralGapCoordinates

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

/-- The exact joint spectral/gap integral of one actual Gaussian
two-by-two block. The density is expressed entirely in explicit scalar
coordinates, so finite products can be transported without frame choices. -/
theorem realPairGaussian_spectralGap_lintegral
    (n : ℝ) (F : ℝ × (ℝ × ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ A in realPairNonrealEntrySet,
      realPairGaussianWeight n A * F (realPairSpectralGapCoordinates A)) =
      ENNReal.ofReal (2*Real.pi) *
        (∫⁻ x : ℝ, ∫⁻ v in realSchurPairCoordinateDomain,
          ENNReal.ofReal (Real.exp (-n*(x^2+v.1))) *
            (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹) *
              ENNReal.ofReal (Real.exp (-(n/2)*v.2)) * F (x,v))) := by
  have hInv : RealPairOrthogonalInvariant (fun A => F (realPairSpectralGapCoordinates A)) := by
    intro Q hQ A
    dsimp only
    rw [realPairSpectralGapCoordinates_conjugation Q A hQ]
  rw [realPairGaussian_nonreal_gap_lintegral n
    (fun A => F (realPairSpectralGapCoordinates A))
    (hF.comp realPairSpectralGapCoordinates_measurable) hInv]
  congr 1
  apply lintegral_congr
  intro x
  apply setLIntegral_congr_fun realSchurPairCoordinateDomain_isOpen.measurableSet
  intro v hv
  dsimp only
  rw [realPairSpectralGapCoordinates_gapBlock x v.1 v.2 hv.1 hv.2]

#print axioms realPairGaussian_spectralGap_lintegral
end SpectralRadiusUpperTail
