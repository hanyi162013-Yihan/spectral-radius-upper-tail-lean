import SpectralRadiusUpperTail.RealMatrixTiltOutlier
import SpectralRadiusUpperTail.FlatSpectralLikelihood

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Conditional lower-bound assembly: the likelihood-cost estimate remains an explicit input. -/
lemma real_spectral_log_lower_of_likelihood_cost
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℝ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℝ) (r : ℝ) (hr : 1 < r) (hb : r < ‖((b/(a+1) : ℝ) : ℂ)‖)
    (C : ℝ)
    (hcost : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) (2*a) b).real
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*C)) < flatSpectralMatrixLikelihood μ (ν n) (2*a) b x})
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -C-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})/(n : ℝ) := by
  apply flatSpectralMatrixTilt_log_lower_from_cost μ (2*a) (by positivity) L ν b
    (fun n => {x : Fin n → Fin n → ℝ | r < (spectralRadius ℂ ((normalizedArray x).map Complex.ofRealHom)).toReal})
  · intro n
    have hm : Measurable (fun x : Fin n → Fin n → ℝ => (normalizedArray x).map Complex.ofRealHom) :=
      (continuous_id.matrix_map Complex.continuous_ofReal).measurable.comp measurable_normalizedArray
    exact measurableSet_lt measurable_const (complex_spectralRadius_measurable.comp hm).ennreal_toReal
  · have ht := real_matrix_spectralTilt_radius_probability μ hm hvar c hc hexp
      a L ha hL ν b r hr hb
    simpa only [Set.compl_setOf,not_lt] using ht
  · exact hcost
  · exact hε

#print axioms real_spectral_log_lower_of_likelihood_cost
end SpectralRadiusUpperTail
