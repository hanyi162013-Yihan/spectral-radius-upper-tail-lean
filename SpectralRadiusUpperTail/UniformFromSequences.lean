import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma uniform_eventually_of_all_sequences (ι : ℕ → Type*) [∀ n, Nonempty (ι n)]
    (P : (n : ℕ) → ι n → Prop)
    (h : ∀ x : (n : ℕ) → ι n, ∀ᶠ n in atTop, P n (x n)) :
    ∀ᶠ n in atTop, ∀ i, P n i := by
  classical
  have hc : ∀ n, ∃ i : ι n, (¬ ∀ j, P n j) → ¬ P n i := by
    intro n
    by_cases hp : ∀ j, P n j
    · exact ⟨Classical.choice inferInstance,fun hn => (hn hp).elim⟩
    · obtain ⟨i,hi⟩ := not_forall.mp hp
      exact ⟨i,fun _ => hi⟩
  choose x hx using hc
  filter_upwards [h x] with n hn
  by_contra hb
  exact hx n hb hn

lemma uniform_small_of_all_sequences (ι : ℕ → Type*) [∀ n, Nonempty (ι n)]
    (f : (n : ℕ) → ι n → ℝ)
    (h : ∀ x : (n : ℕ) → ι n, Tendsto (fun n => f n (x n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i, f n i < ε := by
  apply uniform_eventually_of_all_sequences ι (fun n i => f n i < ε)
  intro x
  exact (tendsto_order.1 (h x)).2 ε hε

#print axioms uniform_eventually_of_all_sequences
#print axioms uniform_small_of_all_sequences
end SpectralRadiusUpperTail
