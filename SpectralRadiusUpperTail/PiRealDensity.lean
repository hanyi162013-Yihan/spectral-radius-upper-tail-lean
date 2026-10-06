import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal

lemma pi_withDensity_ofReal {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) =
      Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
  have (i : ι) : IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (Filter.Eventually.of_forall (hn i))]
    exact ENNReal.ofReal_ne_top
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),Measure.restrict_pi_pi]
  have hi := Integrable.fintype_prod (fun i => (hf i).restrict (s := s i))
  have hnn : ∀ x : ι → E, 0 ≤ ∏ i, f i (x i) := fun x => Finset.prod_nonneg (fun i _ => hn i (x i))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal ((hf i).restrict (s := s i))
    (Filter.Eventually.of_forall (hn i))

#print axioms pi_withDensity_ofReal
end SpectralRadiusUpperTail
