import SpectralRadiusUpperTail.MatrixGramEigenbasis

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {n : ℕ}

noncomputable def eigenvalueActiveSet (lam : Fin n → ℝ) (δ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => δ^2 < lam i)

lemma eigenvalue_active_count (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (δ : ℝ) :
    ((eigenvalueActiveSet lam δ).card : ℝ)*δ^2 ≤ ∑ i, lam i := by
  classical
  calc
    _ = ∑ _i ∈ eigenvalueActiveSet lam δ, δ^2 := by simp
    _ ≤ ∑ i ∈ eigenvalueActiveSet lam δ, lam i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, lam i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro i _ _
      exact hlam i)

lemma eigenvalue_le_sum (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (i : Fin n) :
    lam i ≤ ∑ j, lam j := by
  exact Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i)

#print axioms eigenvalueActiveSet
#print axioms eigenvalue_active_count
#print axioms eigenvalue_le_sum
end SpectralRadiusUpperTail
