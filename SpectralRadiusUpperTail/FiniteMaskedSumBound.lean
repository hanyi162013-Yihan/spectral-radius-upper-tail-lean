import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma finite_masked_sum_le_card_mul {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ i, f i ≤ B) :
    (∑ i, if p i then f i else 0) ≤ (Fintype.card ι : ℝ)*B := by
  calc
    _ ≤ ∑ _i : ι, B := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : p i
      · simpa [hp] using hf i
      · simpa [hp] using hB
    _ = _ := by simp

#print axioms finite_masked_sum_le_card_mul
end SpectralRadiusUpperTail
