import SpectralRadiusUpperTail.ComplexSharpTwoSided
import SpectralRadiusUpperTail.ComplexLinearExpIntegrable
import SpectralRadiusUpperTail.ExponentialBoundsLogLimit

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The sharp complex spectral-radius tail rate. The uniform centered
bulk-concentration estimate is the only remaining analytic input. -/
lemma complex_sharp_log_tail_limit_of_concentration (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (4*c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (hp : (∫ z : ℂ, z^2 ∂μ) = 0)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (r : ℝ) (hr : 1 < r)
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
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) ∧
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ)) atTop (𝓝 (-rate 2 r)) := by
  have htwo := complex_sharp_two_sided_of_concentration μ c hc hexp hm hv hp
    (complex_linear_exp_integrable μ (4*c) (by positivity) hexp) hmgf r hr hconc
  have hmono (n : ℕ) :
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal} ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ (normalizedArray x)).toReal} :=
    by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      intro x hx
      change r < (spectralRadius ℂ (normalizedArray x)).toReal at hx
      change r ≤ (spectralRadius ℂ (normalizedArray x)).toReal
      exact hx.le
  constructor
  · apply tendsto_log_of_exponential_bounds
    intro ε hε
    filter_upwards [htwo ε hε] with n hn
    exact ⟨hn.1, (hmono n).trans hn.2⟩
  · apply tendsto_log_of_exponential_bounds
    intro ε hε
    filter_upwards [htwo ε hε] with n hn
    exact ⟨hn.1.trans (hmono n), hn.2⟩

#print axioms complex_sharp_log_tail_limit_of_concentration
end SpectralRadiusUpperTail
