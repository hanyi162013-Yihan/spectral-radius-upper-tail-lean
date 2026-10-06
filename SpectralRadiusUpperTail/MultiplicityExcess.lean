import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

lemma highMultiplicity_mass_le (d : ι → ℕ) :
    (∑ i, if 3 ≤ d i then d i else 0) ≤ 3 * ∑ i, (d i-2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

lemma highMultiplicity_count_le (d : ι → ℕ) :
    (∑ i, if 3 ≤ d i then 1 else 0) ≤ ∑ i, (d i-2) := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

lemma multiplicity_total_split (d : ι → ℕ) (h : ∀ i, d i ≠ 1) :
    (∑ i, d i) = (∑ i, if 0 < d i then 2 else 0) + ∑ i, (d i-2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := h i
  split_ifs <;> omega

#print axioms highMultiplicity_mass_le
#print axioms highMultiplicity_count_le
#print axioms multiplicity_total_split
end SpectralRadiusUpperTail
