import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

/-- A finite-to-one area formula assembled from countably many injective
Jacobian charts. The sum over chart images records how many marked
preimages lie above each target point. In the marked-eigenline application,
that multiplicity must still be identified with the real-root count. -/
theorem countable_local_area_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (s : ℕ → Set E) (hs : ∀ k, MeasurableSet (s k))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hf' : ∀ k x, x ∈ s k → HasFDerivWithinAt f (f' x) (s k) x)
    (hinj : ∀ k, InjOn f (s k))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ⋃ k, s k, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
      ∫⁻ y, ∑' k, (f '' s k).indicator g y ∂μ := by
  have himage (k : ℕ) : MeasurableSet (f '' s k) :=
    measurable_image_of_fderivWithin (hs k) (hf' k) (hinj k)
  calc
    (∫⁻ x in ⋃ k, s k, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
        ∑' k, ∫⁻ x in s k,
          ENNReal.ofReal |(f' x).det| * g (f x) ∂μ :=
      lintegral_iUnion hs hd _
    _ = ∑' k, ∫⁻ y in f '' s k, g y ∂μ := by
      congr 1
      funext k
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul
        μ (hs k) (hf' k) (hinj k) g).symm
    _ = ∑' k, ∫⁻ y, (f '' s k).indicator g y ∂μ := by
      congr 1
      funext k
      rw [lintegral_indicator (himage k)]
    _ = ∫⁻ y, ∑' k, (f '' s k).indicator g y ∂μ := by
      rw [lintegral_tsum]
      intro k
      exact (hg.indicator (himage k)).aemeasurable

#print axioms countable_local_area_formula
end SpectralRadiusUpperTail
