import SpectralRadiusUpperTail.CountableLocalAreaFormula
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

/-- Area formula for a countable family of injective local charts. The
right-hand side counts overlapping chart images. A marked-eigenline atlas
must be disjointified in the *marked* space before using this as a root
count; disjointifying only the matrix images would erase multiplicity. -/
theorem countable_chart_family_area_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : ℕ → E → E) (f' : ℕ → E → E →L[ℝ] E)
    (s : ℕ → Set E) (hs : ∀ k, MeasurableSet (s k))
    (hf' : ∀ k x, x ∈ s k → HasFDerivWithinAt (f k) (f' k x) (s k) x)
    (hinj : ∀ k, InjOn (f k) (s k))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∑' k, ∫⁻ x in s k,
      ENNReal.ofReal |(f' k x).det| * g (f k x) ∂μ) =
      ∫⁻ y, ∑' k, ((f k) '' s k).indicator g y ∂μ := by
  have himage (k : ℕ) : MeasurableSet ((f k) '' s k) :=
    measurable_image_of_fderivWithin (hs k) (hf' k) (hinj k)
  calc
    (∑' k, ∫⁻ x in s k,
      ENNReal.ofReal |(f' k x).det| * g (f k x) ∂μ) =
        ∑' k, ∫⁻ y in (f k) '' s k, g y ∂μ := by
      congr 1
      funext k
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul
        μ (hs k) (hf' k) (hinj k) g).symm
    _ = ∑' k, ∫⁻ y, ((f k) '' s k).indicator g y ∂μ := by
      congr 1
      funext k
      rw [lintegral_indicator (himage k)]
    _ = ∫⁻ y, ∑' k, ((f k) '' s k).indicator g y ∂μ := by
      rw [lintegral_tsum]
      intro k
      exact (hg.indicator (himage k)).aemeasurable

#print axioms countable_chart_family_area_formula
end SpectralRadiusUpperTail
