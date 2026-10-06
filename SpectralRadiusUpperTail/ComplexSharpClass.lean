import SpectralRadiusUpperTail.SharpPlanarMoment
import SpectralRadiusUpperTail.ComplexClippedDeviationBounds

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The complex matching-class conclusion with the manuscript's sharp planar
MGF assumption. Its square-exponential moment is derived, not assumed.
The bounded-product concentration theorem remains an explicit input. -/
theorem complex_sharp_class_clipped_deviation_bounds
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : SharpPlanarMGF μ) (hcut : CutoffConvexConcentration μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ (normalizedArray x)).toReal) 2 := by
  have hexp : Integrable (fun z : ℂ => Real.exp (4*(1/100)*‖z‖^2)) μ := by
    convert (sharp_planar_squareExp μ hmgf).1 using 1 <;> norm_num
  exact complex_clipped_deviation_bounds_of_cutoff_concentration μ (1/100)
    (by norm_num) hexp hm hv hp (fun u => (hmgf u).2) hcut

/-- The same matching-class endpoint with the convex-distance input exposed. -/
theorem complex_sharp_class_clipped_deviation_bounds_of_talagrand
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : SharpPlanarMGF μ) (hT : CutoffTalagrandHull μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ (normalizedArray x)).toReal) 2 :=
  complex_sharp_class_clipped_deviation_bounds μ hm hv hp hmgf
    (cutoff_concentration_of_talagrand μ hT)

#print axioms complex_sharp_class_clipped_deviation_bounds
#print axioms complex_sharp_class_clipped_deviation_bounds_of_talagrand
end SpectralRadiusUpperTail
