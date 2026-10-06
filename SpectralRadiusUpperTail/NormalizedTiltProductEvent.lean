import SpectralRadiusUpperTail.ChangeMeasure
import Mathlib.MeasureTheory.Measure.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma normalizedTilt_event_eq_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ≥0∞) (A : Set Ω) (hA : MeasurableSet A)
    (hZ : (∫⁻ x, w x ∂μ) ≠ 0) :
    normalizedTilt μ w A = (∫⁻ x in A, w x ∂μ)/(∫⁻ x, w x ∂μ) := by
  rw [normalizedTilt,withDensity_apply _ hA]
  simp only [div_eq_mul_inv]
  exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hZ)

lemma normalizedTilt_prod_event_le {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]
    (ν : Measure V) (μ : Measure X) [SFinite ν] [SFinite μ]
    (w : V × X → ℝ≥0∞) (hw : Measurable w)
    (A : Set X) (hA : MeasurableSet A) (ε : ℝ≥0∞)
    (hZ0 : (∫⁻ p, w p ∂ν.prod μ) ≠ 0) (hZtop : (∫⁻ p, w p ∂ν.prod μ) ≠ ∞)
    (hz0 : ∀ v, (∫⁻ x, w (v,x) ∂μ) ≠ 0)
    (hztop : ∀ v, (∫⁻ x, w (v,x) ∂μ) ≠ ∞)
    (h : ∀ v, normalizedTilt μ (fun x => w (v,x)) A ≤ ε) :
    normalizedTilt (ν.prod μ) w (Set.univ ×ˢ A) ≤ ε := by
  rw [normalizedTilt_event_eq_div _ _ _ (MeasurableSet.univ.prod hA) hZ0]
  apply (ENNReal.div_le_iff hZ0 hZtop).2
  rw [setLIntegral_prod w hw.aemeasurable,Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ v, ε*(∫⁻ x, w (v,x) ∂μ) ∂ν := by
      apply lintegral_mono
      intro v
      have hh := h v
      rw [normalizedTilt_event_eq_div _ _ A hA (hz0 v)] at hh
      exact (ENNReal.div_le_iff (hz0 v) (hztop v)).1 hh
    _ = ε*(∫⁻ v, ∫⁻ x, w (v,x) ∂μ ∂ν) :=
      lintegral_const_mul ε hw.lintegral_prod_right'
    _ = ε*(∫⁻ p, w p ∂ν.prod μ) := by rw [lintegral_prod w hw.aemeasurable]

#print axioms normalizedTilt_event_eq_div
#print axioms normalizedTilt_prod_event_le
end SpectralRadiusUpperTail
