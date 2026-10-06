import SpectralRadiusUpperTail.ComplexMatchingExponential
import SpectralRadiusUpperTail.ComplexBulkFromConvexConcentration
import SpectralRadiusUpperTail.ConvexConcentrationInput

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Matching exponential lower bound with only the bounded-product convex
concentration input remaining. -/
lemma complex_matching_exponential_lower_of_cutoff_concentration
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r)
    (hcut : CutoffConvexConcentration μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 2 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal} := by
  have h2 := squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2
  have hconv := cutoff_concentration_transfer μ (4*c) (by positivity) hexp h2 hcut
  apply complex_matching_exponential_lower_of_bulk_concentration μ hm hvar hpseudo c hc hexp r hr ?_ ε hε
  intro b hb s hs
  obtain ⟨C, hC, q, hq, ht⟩ := complex_bulk_concentration_of_convex_concentration μ h2 hconv
    (s*s) (s/2) (mul_pos hs hs) (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn
  exact hn (b : ℂ)

#print axioms complex_matching_exponential_lower_of_cutoff_concentration
end SpectralRadiusUpperTail
