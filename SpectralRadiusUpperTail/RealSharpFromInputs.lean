import SpectralRadiusUpperTail.RealUpperFromGaussianPower
import SpectralRadiusUpperTail.ExponentialBoundsLogLimit
import SpectralRadiusUpperTail.ClippedDeviationBounds

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Two-sided real matching tails, conditional on the two remaining inputs:
bounded-product concentration and the Gaussian power upper asymptotic. -/
theorem real_class_sharp_two_sided (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1) (h : GaussianEvenMomentDomination μ)
    (hcut : CutoffConvexConcentration μ) (hG : GaussianPowerUpperInput)
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ∧
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) :=
  (real_class_matching_lower μ hsym hvar h r hr hcut ε hε).and
    (real_class_sharp_upper_of_gaussian_power μ hsym h hG r hr ε hε)

theorem real_class_sharp_log_tail_limits (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1) (h : GaussianEvenMomentDomination μ)
    (hcut : CutoffConvexConcentration μ) (hG : GaussianPowerUpperInput)
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) ∧
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have htwo := real_class_sharp_two_sided μ hsym hvar h hcut hG r hr
  have hm (n : ℕ) :
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    change r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal at hx
    exact hx.le
  constructor
  · apply tendsto_log_of_exponential_bounds
    intro ε hε
    filter_upwards [htwo ε hε] with n hn
    exact ⟨hn.1, (hm n).trans hn.2⟩
  · apply tendsto_log_of_exponential_bounds
    intro ε hε
    filter_upwards [htwo ε hε] with n hn
    exact ⟨hn.1.trans (hm n), hn.2⟩

/-- The manuscript's clipped real spectral-radius set bounds. Both missing
analytic inputs remain explicit; this is not an unconditional real LDP. -/
theorem real_class_clipped_deviation_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1) (h : GaussianEvenMomentDomination μ)
    (hcut : CutoffConvexConcentration μ) (hG : GaussianPowerUpperInput) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℝ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal) 1 := by
  apply clipped_deviation_bounds_of_tails _ _ _ 1 (by norm_num)
  exact real_class_sharp_two_sided μ hsym hvar h hcut hG

#print axioms real_class_sharp_two_sided
#print axioms real_class_sharp_log_tail_limits
#print axioms real_class_clipped_deviation_bounds
end SpectralRadiusUpperTail
