import SpectralRadiusUpperTail.StandardGaussianRadialDensity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

lemma haarSphere_embedded_isometry (U : E ≃ₗᵢ[ℝ] E) :
    ((haarSphereProbability (volume : Measure E)).map Subtype.val).map U =
      (haarSphereProbability (volume : Measure E)).map Subtype.val := by
  rw [← stdGaussian_direction_eq_haarSphere]
  have hd : Measurable (fun x : E => ‖x‖⁻¹ • x) := by fun_prop
  rw [Measure.map_map U.continuous.measurable hd]
  have he : (fun x : E => U (‖x‖⁻¹ • x)) = (fun x : E => ‖U x‖⁻¹ • U x) := by
    funext x
    simp
  rw [show (⇑U ∘ fun x : E => ‖x‖⁻¹ • x) =
      ((fun x : E => ‖x‖⁻¹ • x) ∘ ⇑U) from he,
    ← Measure.map_map hd U.continuous.measurable, stdGaussian_map]

lemma haarSphere_lintegral_isometry (U : E ≃ₗᵢ[ℝ] E) (F : E → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ v : sphere (0 : E) 1, F (U v.val) ∂haarSphereProbability (volume : Measure E)) =
      ∫⁻ v : sphere (0 : E) 1, F v.val ∂haarSphereProbability (volume : Measure E) := by
  have he := congrArg (fun μ : Measure E => ∫⁻ x, F x ∂μ)
    (haarSphere_embedded_isometry U)
  have hFU : Measurable (fun x => F (U x)) := hF.comp U.continuous.measurable
  rw [lintegral_map hF U.continuous.measurable,
    lintegral_map hFU measurable_subtype_coe,
    lintegral_map hF measurable_subtype_coe] at he
  exact he

#print axioms haarSphere_embedded_isometry
#print axioms haarSphere_lintegral_isometry
end SpectralRadiusUpperTail
