import SpectralRadiusUpperTail.MatrixWalkProduct
import Mathlib.LinearAlgebra.Matrix.Trace

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Exact closed-walk expansion, with the final edge supplied by B.
This is a finite identity intended for actual trace moment counting. -/
lemma matrixTrace_power_mul_walk_sum (A B : Matrix ι ι R) (k : ℕ) :
    (A^k * B).trace =
      ∑ i, ∑ v : Fin k → ι, matrixWalkTerm A (fun j => B j i) k i v := by
  simp_rw [matrixWalkTerm_sum]
  rfl

lemma matrixTrace_power_mul_edge_sum (A B : Matrix ι ι R) (k : ℕ) :
    (A^k * B).trace = ∑ i, ∑ v : Fin k → ι,
      (∏ a : Fin k, A ((Fin.cons i v : Fin (k+1) → ι) a.castSucc)
        ((Fin.cons i v : Fin (k+1) → ι) a.succ)) *
      B ((Fin.cons i v : Fin (k+1) → ι) (Fin.last k)) i := by
  rw [matrixTrace_power_mul_walk_sum]
  simp only [matrixWalkTerm_product]

#print axioms matrixTrace_power_mul_walk_sum
#print axioms matrixTrace_power_mul_edge_sum
end SpectralRadiusUpperTail
