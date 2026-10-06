import SpectralRadiusUpperTail.RealGaussianPowerUpperProved
import SpectralRadiusUpperTail.TalagrandClassConsequences

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The real matching class has the full clipped spectral-radius
open/closed large-deviation bounds under the entry hypotheses alone. -/
theorem real_class_clipped_deviation_bounds_of_entry_hypotheses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1)
    (h : GaussianEvenMomentDomination μ) :
    ClippedDeviationBounds (fun n => Fin n → Fin n → ℝ)
      (fun n => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
      (fun _ x => (spectralRadius ℂ
        ((normalizedArray x).map Complex.ofRealHom)).toReal) 1 :=
  real_class_clipped_deviation_bounds_of_gaussian_power μ hsym hvar h
    realGaussian_power_upper_proved

theorem real_class_sharp_two_sided_of_entry_hypotheses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1) (h : GaussianEvenMomentDomination μ)
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate 1 r-ε)) ≤
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ∧
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) :=
  real_class_sharp_two_sided μ hsym hvar h
    (cutoff_convex_concentration_proved μ) realGaussian_power_upper_proved r hr ε hε

theorem real_class_sharp_log_tail_limits_of_entry_hypotheses
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ)
    (hvar : (∫ x : ℝ, x^2 ∂μ) = 1) (h : GaussianEvenMomentDomination μ)
    (r : ℝ) (hr : 1 < r) :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) ∧
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r ≤ (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) :=
  real_class_sharp_log_tail_limits μ hsym hvar h
    (cutoff_convex_concentration_proved μ) realGaussian_power_upper_proved r hr

#print axioms real_class_clipped_deviation_bounds_of_entry_hypotheses
#print axioms real_class_sharp_two_sided_of_entry_hypotheses
#print axioms real_class_sharp_log_tail_limits_of_entry_hypotheses
end SpectralRadiusUpperTail
