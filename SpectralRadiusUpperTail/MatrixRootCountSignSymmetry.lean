import SpectralRadiusUpperTail.MatrixCharpolyNegRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Negating a matrix exchanges the positive- and negative-real exterior
root counts, with algebraic multiplicities. -/
theorem matrixPositiveRealRootCount_neg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    matrixPositiveRealRootCount (-A) r =
      matrixNegativeRealRootCount A r := by
  classical
  unfold matrixPositiveRealRootCount matrixNegativeRealRootCount
  rw [matrix_charpoly_neg_roots, Multiset.countP_map,
    Multiset.countP_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro z _
  simp only [Complex.neg_im, Complex.neg_re, neg_eq_zero]
  constructor
  · rintro ⟨him, hr⟩
    exact ⟨him, by linarith⟩
  · rintro ⟨him, hr⟩
    exact ⟨him, by linarith⟩

#print axioms matrixPositiveRealRootCount_neg
end SpectralRadiusUpperTail
