import SpectralRadiusUpperTail.IidWordMoments

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {σ τ υ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [Fintype υ]

lemma entryMultiplicity_sum (e : τ → σ) :
    (∑ i, entryMultiplicity e i) = Fintype.card τ := by
  simpa only [entryMultiplicity, Finset.mem_univ, Finset.filter_true, Finset.card_univ]
    using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset τ) (Finset.univ : Finset σ) e

/-- The set of entry indices used by either word. -/
def entryPairSupport (e : τ → σ) (f : υ → σ) : Finset σ :=
  Finset.univ.filter (fun i => 0 < entryMultiplicity e i + entryMultiplicity f i)

/-- Without a singleton, each used index consumes at least two positions. -/
lemma entryPairSupport_card_le (e : τ → σ) (f : υ → σ)
    (h : ∀ i, entryMultiplicity e i + entryMultiplicity f i ≠ 1) :
    2 * (entryPairSupport e f).card ≤ Fintype.card τ + Fintype.card υ := by
  have hlocal : ∀ i ∈ entryPairSupport e f,
      2 ≤ entryMultiplicity e i + entryMultiplicity f i := by
    intro i hi
    have hp : 0 < entryMultiplicity e i + entryMultiplicity f i :=
      (Finset.mem_filter.mp hi).2
    have hn := h i
    omega
  calc
    2 * (entryPairSupport e f).card = ∑ _i ∈ entryPairSupport e f, (2 : ℕ) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ entryPairSupport e f,
        (entryMultiplicity e i + entryMultiplicity f i) :=
      Finset.sum_le_sum hlocal
    _ ≤ ∑ i : σ, (entryMultiplicity e i + entryMultiplicity f i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = Fintype.card τ + Fintype.card υ := by
      rw [Finset.sum_add_distrib, entryMultiplicity_sum, entryMultiplicity_sum]

#print axioms entryMultiplicity_sum
#print axioms entryPairSupport_card_le
end SpectralRadiusUpperTail
