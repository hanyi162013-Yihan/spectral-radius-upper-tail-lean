import SpectralRadiusUpperTail.MultiplicityExcess

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Only high-multiplicity factors incur a cost; the exponent is controlled
by the excess over two occurrences per used entry. -/
lemma multiplicity_product_excess_bound (d : ι → ℕ) (w : ι → ℝ) (B : ℝ)
    (hB : 1 ≤ B) (hw : ∀ i, 0 ≤ w i)
    (hlow : ∀ i, d i < 3 → w i ≤ 1)
    (hhigh : ∀ i, 3 ≤ d i → w i ≤ B^(d i)) :
    (∏ i, w i) ≤ B^(3*∑ i, (d i-2)) := by
  calc
    _ ≤ ∏ i, B^(if 3 ≤ d i then d i else 0) := by
      apply Finset.prod_le_prod
      · intro i _
        exact hw i
      · intro i _
        by_cases hi : 3 ≤ d i
        · simpa only [if_pos hi] using hhigh i hi
        · simpa only [if_neg hi, pow_zero] using hlow i (by omega)
    _ = B^(∑ i, if 3 ≤ d i then d i else 0) := by rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ _ := pow_le_pow_right₀ hB (highMultiplicity_mass_le d)

#print axioms multiplicity_product_excess_bound
end SpectralRadiusUpperTail
