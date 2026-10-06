import SpectralRadiusUpperTail.ComplexBulkMeanUpperUniform
import SpectralRadiusUpperTail.UpperDeviationFromMean

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma complex_bulk_upper_of_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r)
    (hconc : ∀ R s δ : ℝ, 0 < s → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
              ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
                ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2)) :
    ∃ M : ℝ, 0 < M ∧ ∀ R s ε : ℝ, 0 < s → 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | 2*Real.log ‖z‖+s*M^2+ε < regularizedResidualLogDet x z s/(n : ℝ)} ≤
              C*Real.exp (-q*(n : ℝ)^2) := by
  obtain ⟨M, hM, hmean⟩ := complex_bulk_logDet_mean_upper_uniform μ c hc hexp hm hv r hr
  refine ⟨M, hM, ?_⟩
  intro R s ε hs hε
  obtain ⟨C, hC, q, hq, hbad⟩ := hconc R s (ε/2) hs (by positivity)
  refine ⟨C, hC, q, hq, ?_⟩
  filter_upwards [hmean R s hs (ε/2) (by positivity), hbad] with n hmn hbn z hrz hzR
  exact (upper_event_le_centered_event _ _ (2*Real.log ‖z‖+s*M^2) ε (hmn z hrz hzR)).trans
    (hbn z hrz hzR)

#print axioms complex_bulk_upper_of_concentration
end SpectralRadiusUpperTail
