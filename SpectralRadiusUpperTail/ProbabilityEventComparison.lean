import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma probability_tendsto_zero_of_eventual_subset
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (A B : (n : ℕ) → Set (Ω n))
    (hsub : ∀ᶠ n in atTop, A n ⊆ B n)
    (hB : Tendsto (fun n => (P n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (P n).real (A n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) _ hB
  filter_upwards [hsub] with n hn
  exact measureReal_mono hn (measure_ne_top _ _)

#print axioms probability_tendsto_zero_of_eventual_subset
end SpectralRadiusUpperTail
