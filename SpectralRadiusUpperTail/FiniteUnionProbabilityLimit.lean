import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.Field

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

lemma finite_union_probability_tendsto {ι : Type*} (s : Finset ι)
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (E : ι → (n : ℕ) → Set (Ω n))
    (h : ∀ i ∈ s, Tendsto (fun n => (μ n).real (E i n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real (⋃ i ∈ s, E i n)) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum s h
  simp only [Finset.sum_const_zero] at ht
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => measureReal_biUnion_finset_le s (fun i => E i n)) ht

#print axioms finite_union_probability_tendsto
end SpectralRadiusUpperTail
