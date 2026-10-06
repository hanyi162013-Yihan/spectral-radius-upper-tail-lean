import SpectralRadiusUpperTail.ComplexSharpUpperFromConcentration
import SpectralRadiusUpperTail.ComplexMatchingExponential

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Matching open-tail and closed-tail exponential bounds under the single
remaining uniform centered bulk-concentration hypothesis. -/
lemma complex_sharp_two_sided_of_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r : ℝ) (hr : 1 < r)
    (hconc : ∀ R s δ : ℝ, 0 < s → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
              ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
                ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate 2 r-ε)) ≤
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | r < (spectralRadius ℂ (normalizedArray x)).toReal} ∧
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
          Real.exp ((n : ℝ)*(-rate 2 r+ε)) := by
  have hupper := complex_sharp_upper_of_concentration μ (4*c) (by positivity) hexp
    hm hv hp hint hmgf r hr hconc ε hε
  have hlower := complex_matching_exponential_lower_of_bulk_concentration μ hm hv hp
    c hc hexp r hr ?_ ε hε
  · exact hlower.and hupper
  · intro b hb s hs
    obtain ⟨C, hC, q, hq, hbad⟩ := hconc b (s*s) (s/2) (mul_pos hs hs) (by positivity)
    refine ⟨C, hC, q, hq, ?_⟩
    filter_upwards [hbad] with n hn
    have hnorm : ‖(b : ℂ)‖ = b := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < b)]
    exact hn (b : ℂ) (by simpa only [hnorm] using hb.le) (by simp only [hnorm, le_refl])

#print axioms complex_sharp_two_sided_of_concentration
end SpectralRadiusUpperTail
