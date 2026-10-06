import SpectralRadiusUpperTail.ComplexMatchingFromBulk
import SpectralRadiusUpperTail.BulkLogDetMeanInput
import SpectralRadiusUpperTail.BulkDeviationFromMean

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The exterior bulk mean is proved; only the centered quadratic-speed
concentration estimate remains as an input to this matching lower bound. -/
lemma complex_matching_lower_of_bulk_concentration
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r)
    (hconc : ∀ b : ℝ, r < b → ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | s/2 < |regularizedResidualLogDet x (b : ℂ) (s*s)/(n : ℝ)-
            ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y (b : ℂ) (s*s)/(n : ℝ)
              ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤
            C*Real.exp (-q*(n : ℝ)^2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, -rate 2 r-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ) := by
  apply complex_matching_lower_of_bulk μ hm hvar hpseudo c hc hexp r hr _ ε hε
  intro b hb s hs
  obtain ⟨C, hC, q, hq, hbad⟩ := hconc b hb s hs
  have hmean := complex_bulk_logDet_mean_lower μ (4*c) (by positivity) hexp hm hvar
    b (s*s) (s/2) (hr.trans hb) (mul_pos hs hs) (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [hmean, hbad] with n hn hbn
  exact (lower_event_le_centered_event _ _ (2*Real.log b) s hn).trans hbn

#print axioms complex_matching_lower_of_bulk_concentration
end SpectralRadiusUpperTail
