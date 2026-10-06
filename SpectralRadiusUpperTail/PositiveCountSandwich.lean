import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- If a nonnegative count is either zero or at least one and is bounded by
`N`, its expected value and its positive-event probability differ by at
most the factor `N`. This is the final elementary step in the first-moment
route to a spectral-radius right tail. -/
theorem positive_count_probability_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : Ω → ℝ) (hC : Measurable C)
    (hi : Integrable C μ) (N : ℝ) (hN : 0 ≤ N)
    (hzero : ∀ x, 0 ≤ C x)
    (hgap : ∀ x, 0 < C x → 1 ≤ C x)
    (hbound : ∀ x, C x ≤ N) :
    (∫ x, C x ∂μ) ≤ N * μ.real {x | 0 < C x} ∧
      μ.real {x | 0 < C x} ≤ ∫ x, C x ∂μ := by
  let E := {x | 0 < C x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hC
  have hI : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hpoint_left (x : Ω) : C x ≤ N * E.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, mul_one]
      exact hbound x
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact le_of_not_gt hx
  have hpoint_right (x : Ω) :
      E.indicator (fun _ => (1 : ℝ)) x ≤ C x := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      exact hgap x hx
    · rw [Set.indicator_of_notMem hx]
      exact hzero x
  constructor
  · have h := integral_mono hi (hI.const_mul N) hpoint_left
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hE] at h
    simpa only [smul_eq_mul, mul_one] using h
  · have h := integral_mono hI hi hpoint_right
    rw [integral_indicator_const (1 : ℝ) hE] at h
    simpa only [smul_eq_mul, mul_one] using h

#print axioms positive_count_probability_sandwich
end SpectralRadiusUpperTail
