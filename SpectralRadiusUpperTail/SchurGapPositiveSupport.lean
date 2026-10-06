import SpectralRadiusUpperTail.SchurGapKernelLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The zero gap has zero mass under the actual continuous gap law. -/
theorem schurSquaredGapLaw_positive (n y : ℝ) (hn : 0 < n) :
    ∀ᵐ s ∂schurSquaredGapLaw n y, 0 < s := by
  have hac : schurSquaredGapLaw n y ≪ (volume : Measure ℝ) := by
    rw [schurSquaredGapLaw_eq_explicitDensity]
    exact withDensity_absolutelyContinuous _ _
  have hzero : ∀ᵐ s ∂schurSquaredGapLaw n y, s ≠ 0 :=
    (Measure.ae_le_iff_absolutelyContinuous.mpr hac) ((volume : Measure ℝ).ae_ne 0)
  filter_upwards [schurSquaredGapLaw_nonnegative n y hn,hzero] with s hs hs0
  exact lt_of_le_of_ne hs hs0.symm

#print axioms schurSquaredGapLaw_positive
end SpectralRadiusUpperTail
