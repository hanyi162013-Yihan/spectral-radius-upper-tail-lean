import SpectralRadiusUpperTail.ComplexSharpLogTailLimit
import SpectralRadiusUpperTail.ComplexBulkFromConvexConcentration
import SpectralRadiusUpperTail.ConvexConcentrationInput

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The actual complex sharp tail rate, with only the bounded-product convex
concentration input remaining. Every matrix and truncation step is discharged. -/
lemma complex_sharp_log_tail_limit_of_cutoff_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r : ℝ) (hr : 1 < r)
    (hcut : CutoffConvexConcentration μ) :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) ∧
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) := by
  have h2 := squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2
  have hconv := cutoff_concentration_transfer μ (4*c) (by positivity) hexp h2 hcut
  apply complex_sharp_log_tail_limit_of_concentration μ c hc hexp hm hv hp hmgf r hr
  intro R s δ hs hδ
  obtain ⟨C, hC, q, hq, ht⟩ := complex_bulk_concentration_of_convex_concentration μ h2 hconv s δ hs hδ
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn z _ _
  exact hn z

#print axioms complex_sharp_log_tail_limit_of_cutoff_concentration
end SpectralRadiusUpperTail
