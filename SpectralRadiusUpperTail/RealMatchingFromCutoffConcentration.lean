import SpectralRadiusUpperTail.RealMatchingExponential
import SpectralRadiusUpperTail.RealBulkFromConvexConcentration
import SpectralRadiusUpperTail.ConvexConcentrationInput

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Matching exponential lower bound with only the bounded-product convex
concentration input remaining. -/
lemma real_matching_exponential_lower_of_cutoff_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r)
    (hcut : CutoffConvexConcentration μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} := by
  have h2 := squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2
  have hconv := cutoff_concentration_transfer μ (4*c) (by positivity) hexp h2 hcut
  apply real_matching_exponential_lower_of_bulk_concentration μ hm hvar c hc hexp r hr ?_ ε hε
  intro b hb s hs
  obtain ⟨C, hC, q, hq, ht⟩ := real_bulk_concentration_of_convex_concentration μ h2 hconv
    (s*s) (s/2) (mul_pos hs hs) (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [ht] with n hn
  exact hn b

#print axioms real_matching_exponential_lower_of_cutoff_concentration
end SpectralRadiusUpperTail
