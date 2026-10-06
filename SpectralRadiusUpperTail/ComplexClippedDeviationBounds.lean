import SpectralRadiusUpperTail.ClippedDeviationBounds
import SpectralRadiusUpperTail.ComplexSharpFromTalagrand

namespace SpectralRadiusUpperTail
open MeasureTheory Filter

/-- Actual clipped complex iid spectral radii max(1,ρ) satisfy all exponential
open/closed set estimates, including rate zero at one and impossible sets below
one, conditional only on bounded-product convex concentration. -/
lemma complex_clipped_deviation_bounds_of_cutoff_concentration
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (hcut : CutoffConvexConcentration μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ (normalizedArray x)).toReal) 2 := by
  have h2 := squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2
  have hconv := cutoff_concentration_transfer μ (4*c) (by positivity) hexp h2 hcut
  have hint := complex_linear_exp_integrable μ (4*c) (by positivity) hexp
  apply clipped_deviation_bounds_of_tails _ _ _ 2 (by norm_num)
  intro r hr ε hε
  apply complex_sharp_two_sided_of_concentration μ c hc hexp hm hv hp hint hmgf r hr ?_ ε hε
  intro R s δ hs hδ
  obtain ⟨C, hC, q, hq, ht⟩ := complex_bulk_concentration_of_convex_concentration μ h2 hconv s δ hs hδ
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn z _ _
  exact hn z

lemma complex_clipped_deviation_bounds_of_talagrand
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (hT : CutoffTalagrandHull μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℂ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ (normalizedArray x)).toReal) 2 :=
  complex_clipped_deviation_bounds_of_cutoff_concentration μ c hc hexp hm hv hp hmgf
    (cutoff_concentration_of_talagrand μ hT)

#print axioms complex_clipped_deviation_bounds_of_cutoff_concentration
#print axioms complex_clipped_deviation_bounds_of_talagrand
end SpectralRadiusUpperTail
