import SpectralRadiusUpperTail.ComplexMatrixTiltOutlier
import SpectralRadiusUpperTail.FlatSpectralLikelihood

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Conditional lower-bound assembly: the likelihood-cost estimate remains an explicit input. -/
lemma complex_spectral_log_lower_of_likelihood_cost
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (ν : (n : ℕ) → Measure (flatUnitDirections ℂ n L)) [∀ n, IsProbabilityMeasure (ν n)]
    (b : ℂ) (r : ℝ) (hr : 1 < r) (hb : r < ‖(b/((a+1 : ℝ) : ℂ))‖)
    (C : ℝ)
    (hcost : Tendsto (fun n => (flatSpectralMatrixTilt μ (ν n) a b).real
      {x | ENNReal.ofReal (Real.exp ((n : ℝ)*C)) < flatSpectralMatrixLikelihood μ (ν n) a b x})
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, -C-ε ≤
      Real.log ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        {x | r < (spectralRadius ℂ (normalizedArray x)).toReal})/(n : ℝ) := by
  apply flatSpectralMatrixTilt_log_lower_from_cost μ a (by positivity) L ν b
    (fun n => {x : Fin n → Fin n → ℂ | r < (spectralRadius ℂ (normalizedArray x)).toReal})
  · intro n
    exact measurableSet_lt measurable_const
      (complex_spectralRadius_measurable.comp measurable_normalizedArray).ennreal_toReal
  · have ht := complex_matrix_spectralTilt_radius_probability μ hm hvar hpseudo c hc hexp
      a L ha hL ν b r hr hb
    simpa only [Set.compl_setOf,not_lt] using ht
  · exact hcost
  · exact hε

#print axioms complex_spectral_log_lower_of_likelihood_cost
end SpectralRadiusUpperTail
