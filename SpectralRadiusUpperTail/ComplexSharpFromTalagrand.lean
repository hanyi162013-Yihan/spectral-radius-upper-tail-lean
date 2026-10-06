import SpectralRadiusUpperTail.ComplexSharpFromCutoffConcentration
import SpectralRadiusUpperTail.CutoffTalagrandInput

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Actual complex sharp tails, conditional only on the stated classical
product-measure convex-distance input. All application-specific steps are proved. -/
lemma complex_sharp_log_tail_limit_of_talagrand (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r : ℝ) (hr : 1 < r)
    (hT : CutoffTalagrandHull μ) :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) ∧
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) := by
  exact complex_sharp_log_tail_limit_of_cutoff_concentration μ c hc hexp hm hv hp hmgf r hr
    (cutoff_concentration_of_talagrand μ hT)

#print axioms complex_sharp_log_tail_limit_of_talagrand
end SpectralRadiusUpperTail
