import SpectralRadiusUpperTail.ComplexMatchingFromConcentration
import SpectralRadiusUpperTail.ComplexTailPositive

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The matching lower estimate stated directly for probabilities. -/
lemma complex_matching_exponential_lower_of_bulk_concentration
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
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 2 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal} := by
  filter_upwards [complex_matching_lower_of_bulk_concentration μ hm hvar hpseudo c hc hexp
      r hr hconc ε hε,
    complex_spectral_tail_eventually_positive μ hm hvar hpseudo c hc hexp r hr,
    eventually_gt_atTop 0] with n hn hp hn0
  exact exponential_lower_of_log_lower _ _ _ n hp hn0 hn

#print axioms complex_matching_exponential_lower_of_bulk_concentration
end SpectralRadiusUpperTail
