import SpectralRadiusUpperTail.MatrixWalkProduct
import Mathlib.Analysis.RCLike.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]

noncomputable def matrixBilinearPathTerm (A : Matrix ι ι 𝕂) (p q : ι → 𝕂)
    (k : ℕ) (v : Fin (k+1) → ι) : 𝕂 :=
  star (p (v 0)) * (∏ a : Fin k, A (v a.castSucc) (v a.succ)) * q (v (Fin.last k))

lemma matrixBilinearPathTerm_split (A : Matrix ι ι 𝕂) (p q : ι → 𝕂)
    (k : ℕ) (i : ι) (v : Fin k → ι) :
    matrixBilinearPathTerm A p q k (Fin.cons i v) =
      star (p i) * matrixWalkTerm A q k i v := by
  rw [matrixWalkTerm_product]
  simp only [matrixBilinearPathTerm, Fin.cons_zero, mul_assoc]

/-- A genuine matrix-power bilinear form expanded over all vertex paths. -/
lemma matrixBilinearPathTerm_sum (A : Matrix ι ι 𝕂) (p q : ι → 𝕂) (k : ℕ) :
    (∑ v : Fin (k+1) → ι, matrixBilinearPathTerm A p q k v) =
      ∑ i, star (p i) * (A^k).mulVec q i := by
  calc
    _ = ∑ z : ι × (Fin k → ι),
        matrixBilinearPathTerm A p q k ((matrixWalkSplit k).symm z) :=
      ((matrixWalkSplit k).symm.sum_comp _).symm
    _ = ∑ i, ∑ v : Fin k → ι, star (p i) * matrixWalkTerm A q k i v := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro v _
      exact matrixBilinearPathTerm_split A p q k i v
    _ = _ := by simp only [← Finset.mul_sum, matrixWalkTerm_sum]

#print axioms matrixBilinearPathTerm
#print axioms matrixBilinearPathTerm_split
#print axioms matrixBilinearPathTerm_sum
end SpectralRadiusUpperTail
