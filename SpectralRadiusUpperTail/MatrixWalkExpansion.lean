import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]

/-- A directed walk term, including its terminal test-vector coefficient. -/
def matrixWalkTerm (A : Matrix ι ι R) (q : ι → R) :
    (k : ℕ) → ι → (Fin k → ι) → R
  | 0, i, _ => q i
  | k+1, i, v => A i (v 0)*matrixWalkTerm A q k (v 0) (fun j => v j.succ)

def matrixWalkSplit (k : ℕ) : (Fin (k+1) → ι) ≃ ι × (Fin k → ι) where
  toFun v := (v 0, fun j => v j.succ)
  invFun v := Fin.cons v.1 v.2
  left_inv v := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  right_inv v := by
    rcases v with ⟨i,v⟩
    rfl

/-- Actual matrix powers acting on a vector equal the sum over directed walks. -/
lemma matrixWalkTerm_sum (A : Matrix ι ι R) (q : ι → R) (k : ℕ) (i : ι) :
    (∑ v : Fin k → ι, matrixWalkTerm A q k i v) = (A^k).mulVec q i := by
  induction k generalizing i with
  | zero => simp [matrixWalkTerm]
  | succ k ih =>
    calc
      _ = ∑ p : ι × (Fin k → ι), matrixWalkTerm A q (k+1) i ((matrixWalkSplit k).symm p) :=
        ((matrixWalkSplit k).symm.sum_comp _).symm
      _ = ∑ j, ∑ v : Fin k → ι, A i j*matrixWalkTerm A q k j v := by
        rw [Fintype.sum_prod_type]
        rfl
      _ = ∑ j, A i j*(A^k).mulVec q j := by
        simp only [← Finset.mul_sum, ih]
      _ = (A^(k+1)).mulVec q i := by
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        rfl

#print axioms matrixWalkTerm_sum
end SpectralRadiusUpperTail
