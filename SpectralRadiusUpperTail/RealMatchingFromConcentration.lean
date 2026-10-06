import SpectralRadiusUpperTail.RealMatchingFromBulk
import SpectralRadiusUpperTail.BulkLogDetMeanInput
import SpectralRadiusUpperTail.BulkDeviationFromMean

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The exterior bulk mean is proved; only the centered quadratic-speed
concentration estimate remains as an input to this matching lower bound. -/
lemma real_matching_lower_of_bulk_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (r : ℝ) (hr : 1 < r)
    (hconc : ∀ b : ℝ, r < b → ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | s/2 < |regularizedResidualLogDet x (b : ℝ) (s*s)/(n : ℝ)-
            ∫ y : Fin n → Fin n → ℝ, regularizedResidualLogDet y (b : ℝ) (s*s)/(n : ℝ)
              ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤
            C*Real.exp (-q*(n : ℝ)^2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, -rate 1 r-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ) := by
  apply real_matching_lower_of_bulk μ hm hvar c hc hexp r hr _ ε hε
  intro b hb s hs
  obtain ⟨C, hC, q, hq, hbad⟩ := hconc b hb s hs
  have hmean := real_bulk_logDet_mean_lower μ (4*c) (by positivity) hexp hm hvar
    b (s*s) (s/2) (hr.trans hb) (mul_pos hs hs) (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [hmean, hbad] with n hn hbn
  exact (lower_event_le_centered_event _ _ (2*Real.log b) s hn).trans hbn

#print axioms real_matching_lower_of_bulk_concentration
end SpectralRadiusUpperTail
