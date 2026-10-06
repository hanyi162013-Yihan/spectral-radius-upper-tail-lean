import SpectralRadiusUpperTail.MatrixBilinearPaths
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Star.BigOperators

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]

/-- The product with its conjugate is exactly the sum over paired vertex paths. -/
lemma matrixBilinear_pair_expansion (A : Matrix ι ι 𝕂) (p q : ι → 𝕂) (k : ℕ) :
    (∑ i, star (p i) * (A^k).mulVec q i) *
      star (∑ i, star (p i) * (A^k).mulVec q i) =
    ∑ x : (Fin (k+1) ⊕ Fin (k+1)) → ι,
      matrixBilinearPathTerm A p q k (fun a => x (Sum.inl a)) *
        star (matrixBilinearPathTerm A p q k (fun a => x (Sum.inr a))) := by
  rw [← matrixBilinearPathTerm_sum A p q k, star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have hprod : (∑ z : (Fin (k+1) → ι) × (Fin (k+1) → ι),
      matrixBilinearPathTerm A p q k z.1 * star (matrixBilinearPathTerm A p q k z.2)) =
      ∑ v : Fin (k+1) → ι, ∑ w : Fin (k+1) → ι,
        matrixBilinearPathTerm A p q k v * star (matrixBilinearPathTerm A p q k w) := by
    rw [Fintype.sum_prod_type]
  rw [← hprod]
  exact (Equiv.sumArrowEquivProdArrow (Fin (k+1)) (Fin (k+1)) ι).sum_comp
    (fun z => matrixBilinearPathTerm A p q k z.1 *
      star (matrixBilinearPathTerm A p q k z.2)) |>.symm

#print axioms matrixBilinear_pair_expansion
end SpectralRadiusUpperTail
