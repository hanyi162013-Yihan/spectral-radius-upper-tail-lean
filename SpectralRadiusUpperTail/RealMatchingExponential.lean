import SpectralRadiusUpperTail.RealMatchingFromConcentration
import SpectralRadiusUpperTail.RealTailPositive

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The real matching lower bound in direct exponential probability form. -/
lemma real_matching_exponential_lower_of_bulk_concentration
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
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} := by
  filter_upwards [real_matching_lower_of_bulk_concentration μ hm hvar c hc hexp
      r hr hconc ε hε,
    real_spectral_tail_eventually_positive μ hm hvar c hc hexp r hr,
    eventually_gt_atTop 0] with n hn hp hn0
  exact exponential_lower_of_log_lower _ _ _ n hp hn0 hn

#print axioms real_matching_exponential_lower_of_bulk_concentration
end SpectralRadiusUpperTail
