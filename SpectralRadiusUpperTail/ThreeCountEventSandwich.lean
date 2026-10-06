import SpectralRadiusUpperTail.PositiveCountSandwich
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- A target event caught between one positive count and the union of
three positive-count events inherits first-moment bounds. -/
theorem three_count_event_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : Fin 3 → Ω → ℝ)
    (hC : ∀ i, Measurable (C i))
    (hInt : ∀ i, Integrable (C i) μ)
    (N : ℝ) (hN : 0 < N)
    (hzero : ∀ i x, 0 ≤ C i x)
    (hgap : ∀ i x, 0 < C i x → 1 ≤ C i x)
    (hbound : ∀ i x, C i x ≤ N)
    (E : Set Ω)
    (hlower : {x | 0 < C 0 x} ⊆ E)
    (hupper : E ⊆ {x | 0 < C 0 x} ∪
      {x | 0 < C 1 x} ∪ {x | 0 < C 2 x}) :
    (∫ x, C 0 x ∂μ)/N ≤ μ.real E ∧
    μ.real E ≤ (∫ x, C 0 x ∂μ) +
      (∫ x, C 1 x ∂μ) + (∫ x, C 2 x ∂μ) := by
  have h0 := positive_count_probability_sandwich μ (C 0)
    (hC 0) (hInt 0) N hN.le (hzero 0) (hgap 0) (hbound 0)
  have h1 := positive_count_probability_sandwich μ (C 1)
    (hC 1) (hInt 1) N hN.le (hzero 1) (hgap 1) (hbound 1)
  have h2 := positive_count_probability_sandwich μ (C 2)
    (hC 2) (hInt 2) N hN.le (hzero 2) (hgap 2) (hbound 2)
  constructor
  · have hm := measureReal_mono (μ := μ) hlower
    have hdiv : (∫ x, C 0 x ∂μ)/N ≤ μ.real {x | 0 < C 0 x} :=
      (div_le_iff₀ hN).2 (by simpa only [mul_comm] using h0.1)
    exact hdiv.trans hm
  · have hm := measureReal_mono (μ := μ) hupper
    have hu := measureReal_union_le (μ := μ)
      ({x | 0 < C 0 x} ∪ {x | 0 < C 1 x})
      {x | 0 < C 2 x}
    have hu' := measureReal_union_le (μ := μ)
      {x | 0 < C 0 x} {x | 0 < C 1 x}
    linarith [h0.2, h1.2, h2.2]

#print axioms three_count_event_sandwich
end SpectralRadiusUpperTail
