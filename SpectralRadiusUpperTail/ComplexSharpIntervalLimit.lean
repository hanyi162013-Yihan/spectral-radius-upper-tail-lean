import SpectralRadiusUpperTail.ComplexSharpLogTailLimit
import SpectralRadiusUpperTail.TailIntervalBounds

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Local interval probabilities have the rate at the left endpoint. The
remaining concentration hypothesis is retained explicitly. -/
lemma complex_sharp_interval_log_limit_of_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r b : ℝ) (hr : 1 < r) (hrb : r < b)
    (hconc : ∀ R s δ : ℝ, 0 < s → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
            {x | δ < |regularizedResidualLogDet x z s/(n : ℝ)-
              ∫ y : Fin n → Fin n → ℂ, regularizedResidualLogDet y z s/(n : ℝ)
                ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2))
 :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal ∧
          (spectralRadius ℂ (normalizedArray x)).toReal < b})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) := by
  have hint := complex_linear_exp_integrable μ (4*c) (by positivity : 0 < 4*c) hexp
  have htwo := complex_sharp_two_sided_of_concentration μ c hc hexp hm hv hp hint hmgf r hr hconc
  have hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | b ≤ (spectralRadius ℂ (normalizedArray x)).toReal} ≤
          Real.exp ((n : ℝ)*(-rate 2 b+ε)) := by
    intro ε hε
    apply complex_sharp_upper_of_concentration μ (4*c) (by positivity) hexp
      hm hv hp hint hmgf b (hr.trans hrb) ?_ ε hε
    intro R s δ hs hδ
    obtain ⟨C, hC, q, hq, ht⟩ := hconc R s δ hs hδ
    refine ⟨C, hC, q, hq, ?_⟩
    filter_upwards [ht] with n hn z hz hzR
    exact hn z (hrb.le.trans hz) hzR
  apply tendsto_log_of_exponential_bounds
  intro ε hε
  have hl := interval_exponential_lower_of_tails
    (fun n => Fin n → Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (fun n x => (spectralRadius ℂ (normalizedArray x)).toReal)
    r b (rate 2 r) (rate 2 b) (rate_strict_mono 2 r b (by norm_num) hr.le hrb)
    (fun δ hδ => (htwo δ hδ).mono (fun _ hn => hn.1)) hupper ε hε
  filter_upwards [hl, htwo ε hε] with n hn hu
  refine ⟨hn, ?_⟩
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hu.2
  intro x hx
  change r < (spectralRadius ℂ (normalizedArray x)).toReal ∧
    (spectralRadius ℂ (normalizedArray x)).toReal < b at hx
  change r ≤ (spectralRadius ℂ (normalizedArray x)).toReal
  exact hx.1.le

#print axioms complex_sharp_interval_log_limit_of_concentration
end SpectralRadiusUpperTail
