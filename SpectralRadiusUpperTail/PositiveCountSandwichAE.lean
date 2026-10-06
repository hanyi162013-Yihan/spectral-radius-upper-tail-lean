import SpectralRadiusUpperTail.PositiveCountSandwich
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The first-moment count sandwich only needs almost-everywhere
measurability. This is useful when a measurable spectral ordering is
constructed on the simple-spectrum locus. -/
theorem positive_count_probability_sandwich_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : Ω → ℝ) (hC : AEMeasurable C μ)
    (hi : Integrable C μ) (N : ℝ)
    (hzero : ∀ x, 0 ≤ C x)
    (hgap : ∀ x, 0 < C x → 1 ≤ C x)
    (hbound : ∀ x, C x ≤ N) :
    (∫ x, C x ∂μ) ≤ N * μ.real {x | 0 < C x} ∧
      μ.real {x | 0 < C x} ≤ ∫ x, C x ∂μ := by
  let D := hC.mk C
  have hD : Measurable D := hC.measurable_mk
  have heq : C =ᵐ[μ] D := hC.ae_eq_mk
  have hiD : Integrable D μ := hi.congr heq
  let E := {x | 0 < D x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hD
  have hI : Integrable (E.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const _).indicator hE
  have hleft : ∀ᵐ x ∂μ,
      D x ≤ N * E.indicator (fun _ : Ω => (1 : ℝ)) x := by
    filter_upwards [heq] with x hx
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, mul_one]
      rw [← hx]
      exact hbound x
    · rw [Set.indicator_of_notMem hxE, mul_zero]
      rw [← hx]
      apply le_of_not_gt
      intro hpos
      apply hxE
      change 0 < D x
      rwa [← hx]
  have hright : ∀ᵐ x ∂μ,
      E.indicator (fun _ : Ω => (1 : ℝ)) x ≤ D x := by
    filter_upwards [heq] with x hx
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, ← hx]
      have hpos : 0 < C x := by
        change 0 < D x at hxE
        rwa [← hx] at hxE
      exact hgap x hpos
    · rw [Set.indicator_of_notMem hxE, ← hx]
      exact hzero x
  have hmeasure : μ.real {x | 0 < C x} = μ.real E := by
    have hsets : {x | 0 < C x} =ᵐ[μ] E := by
      filter_upwards [heq] with x hx
      change (0 < C x) = (0 < D x)
      rw [hx]
    exact congrArg ENNReal.toReal hsets.measure_eq
  constructor
  · have h := integral_mono_ae hiD (hI.const_mul N) hleft
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hE] at h
    rw [integral_congr_ae heq, hmeasure]
    simpa only [smul_eq_mul, mul_one] using h
  · have h := integral_mono_ae hI hiD hright
    rw [integral_indicator_const (1 : ℝ) hE] at h
    rw [integral_congr_ae heq, hmeasure]
    simpa only [smul_eq_mul, mul_one] using h

#print axioms positive_count_probability_sandwich_ae
end SpectralRadiusUpperTail
