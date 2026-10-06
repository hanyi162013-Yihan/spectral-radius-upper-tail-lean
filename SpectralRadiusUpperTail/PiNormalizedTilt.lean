import SpectralRadiusUpperTail.PiRealDensity
import SpectralRadiusUpperTail.ChangeMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal

lemma normalizedTilt_ofReal_eq_density {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ f x) (hp : 0 < ∫ x, f x ∂μ) :
    normalizedTilt μ (fun x => ENNReal.ofReal (f x)) =
      μ.withDensity (fun x => ENNReal.ofReal (f x/(∫ y, f y ∂μ))) := by
  rw [normalizedTilt,← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn)]
  congr 1
  funext x
  exact (ENNReal.ofReal_div_of_pos hp).symm

lemma pi_normalizedTilt_ofReal {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hn : ∀ i x, 0 ≤ f i x) (hp : ∀ i, 0 < ∫ x, f i x ∂μ i) :
    normalizedTilt (Measure.pi μ) (fun x => ENNReal.ofReal (∏ i, f i (x i))) =
      Measure.pi (fun i => normalizedTilt (μ i) (fun x => ENNReal.ofReal (f i x))) := by
  have hi := Integrable.fintype_prod hf
  have hpall : 0 < ∫ x : ι → E, (∏ i, f i (x i)) ∂Measure.pi μ := by
    rw [integral_fintype_prod_eq_prod (μ := μ) f]
    exact Finset.prod_pos (fun i _ => hp i)
  rw [normalizedTilt_ofReal_eq_density _ _ hi
    (fun x => Finset.prod_nonneg (fun i _ => hn i (x i))) hpall,
    integral_fintype_prod_eq_prod (μ := μ) f]
  simp_rw [← Finset.prod_div_distrib]
  rw [pi_withDensity_ofReal μ (fun i x => f i x/(∫ y, f i y ∂μ i))
    (fun i => (hf i).div_const _) (fun i x => div_nonneg (hn i x) (hp i).le)]
  congr 1
  funext i
  exact (normalizedTilt_ofReal_eq_density (μ i) (f i) (hf i) (hn i) (hp i)).symm

#print axioms normalizedTilt_ofReal_eq_density
#print axioms pi_normalizedTilt_ofReal
end SpectralRadiusUpperTail
