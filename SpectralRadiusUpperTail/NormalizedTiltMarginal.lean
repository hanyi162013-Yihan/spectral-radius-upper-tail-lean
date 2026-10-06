import SpectralRadiusUpperTail.NormalizedTiltProductEvent

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_prod_snd (V X : Type*) [MeasurableSpace V] [MeasurableSpace X]
    (ν : Measure V) (μ : Measure X) [SFinite ν] [SFinite μ]
    (w : V × X → ℝ≥0∞) (hw : Measurable w)
    (hZ0 : (∫⁻ p, w p ∂ν.prod μ) ≠ 0) :
    (normalizedTilt (ν.prod μ) w).map Prod.snd =
      normalizedTilt μ (fun x => ∫⁻ v, w (v,x) ∂ν) := by
  have he : (∫⁻ p, w p ∂ν.prod μ) = ∫⁻ x, ∫⁻ v, w (v,x) ∂ν ∂μ :=
    lintegral_prod_symm w hw.aemeasurable
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  have heA : (Prod.snd : V × X → X) ⁻¹' A = Set.univ ×ˢ A := by ext p; simp
  rw [heA]
  rw [normalizedTilt_event_eq_div _ _ _ (MeasurableSet.univ.prod hA) hZ0,
    normalizedTilt_event_eq_div _ _ _ hA (by rwa [← he]),
    setLIntegral_prod_symm w hw.aemeasurable,Measure.restrict_univ,he]

#print axioms normalizedTilt_prod_snd
end SpectralRadiusUpperTail
