import SpectralRadiusUpperTail.ChangeMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

lemma probability_inter_ge_one_sub_compl {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    1-μ.real Aᶜ-μ.real Bᶜ ≤ μ.real (A ∩ B) := by
  have hu := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  have he := measureReal_add_measureReal_compl (μ := μ) (hA.inter hB)
  rw [Set.compl_inter] at he
  have h1 : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [h1] at he
  linarith

lemma probability_inter_eventually_half
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A B : (n : ℕ) → Set (Ω n))
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (ha : Tendsto (fun n => (μ n).real (A n)ᶜ) atTop (𝓝 0))
    (hb : Tendsto (fun n => (μ n).real (B n)ᶜ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1/2 ≤ (μ n).real (A n ∩ B n) := by
  have hla := (tendsto_order.1 ha).2 (1/4) (by norm_num)
  have hlb := (tendsto_order.1 hb).2 (1/4) (by norm_num)
  filter_upwards [hla,hlb] with n hn hm
  have hh := probability_inter_ge_one_sub_compl (μ n) (A n) (B n) (hA n) (hB n)
  linarith

#print axioms probability_inter_ge_one_sub_compl
#print axioms probability_inter_eventually_half
end SpectralRadiusUpperTail
