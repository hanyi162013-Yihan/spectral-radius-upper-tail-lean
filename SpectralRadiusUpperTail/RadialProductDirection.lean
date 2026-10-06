import SpectralRadiusUpperTail.NormalizedTiltMap

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_prod_radial_direction {S R : Type*}
    [MeasurableSpace S] [MeasurableSpace R] (ν : Measure S) [IsFiniteMeasure ν] [NeZero ν]
    (μ : Measure R) [SFinite μ] (g : R → ℝ≥0∞) (hg : Measurable g)
    (hg0 : (∫⁻ r, g r ∂μ) ≠ 0) (hgtop : (∫⁻ r, g r ∂μ) ≠ ∞) :
    (normalizedTilt (ν.prod μ) (fun p => g p.2)).map Prod.fst =
      normalizedTilt ν (fun _ => 1) := by
  have hs0 : ν Set.univ ≠ 0 := NeZero.ne _
  have hw : Measurable (fun p : S × R => g p.2) := hg.comp measurable_snd
  have hZ : (∫⁻ p : S × R, g p.2 ∂ν.prod μ) = (∫⁻ r, g r ∂μ)*ν Set.univ := by
    rw [lintegral_prod _ hw.aemeasurable]
    simp
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA]
  have heA : (Prod.fst : S × R → S) ⁻¹' A = A ×ˢ Set.univ := by ext p; simp
  rw [heA,normalizedTilt_event_eq_div _ _ _ (hA.prod MeasurableSet.univ)
    (by rw [hZ]; exact mul_ne_zero hg0 hs0),
    normalizedTilt_event_eq_div _ _ _ hA (by simpa using hs0),
    setLIntegral_prod _ hw.aemeasurable,Measure.restrict_univ,hZ]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  exact ENNReal.mul_div_mul_left _ _ hg0 hgtop

#print axioms normalizedTilt_prod_radial_direction
end SpectralRadiusUpperTail
