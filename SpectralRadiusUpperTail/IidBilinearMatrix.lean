import SpectralRadiusUpperTail.IidBilinearMoment
import SpectralRadiusUpperTail.ActualMatrixIdentity
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {N : ℕ}

/-- The product-space coefficient is exactly the bilinear form of the actual
normalized entry matrix, with the same normalization as the coupling identity. -/
lemma iidBilinear_eq_normalized_matrix (p q : Fin N → 𝕂) (x : Fin N × Fin N → 𝕂) :
    iidBilinear p q x = ∑ i, star (p i)*
      ((normalizedArray (fun i j => x (i,j))).mulVec q) i := by
  simp only [iidBilinear, Fintype.sum_prod_type, Matrix.mulVec, dotProduct,
    normalizedArray, Finset.mul_sum, RCLike.real_smul_eq_coe_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms iidBilinear_eq_normalized_matrix
end SpectralRadiusUpperTail
