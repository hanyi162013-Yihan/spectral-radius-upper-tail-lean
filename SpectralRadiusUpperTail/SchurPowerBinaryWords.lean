import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A noncommutative word in the diagonal and strictly upper terms.
`true` chooses the diagonal term at that position. -/
def schurBinaryWord {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (D U : Matrix ι ι R) : (k : ℕ) → (Fin k → Bool) → Matrix ι ι R
  | 0, _ => 1
  | k+1, w => (if w 0 then D else U) * schurBinaryWord D U k (fun j => w j.succ)

/-- Exact noncommutative expansion of the full matrix power. -/
theorem schur_power_binary_word_sum {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Semiring R] (D U : Matrix ι ι R) (k : ℕ) :
    (D+U)^k = ∑ w : Fin k → Bool, schurBinaryWord D U k w := by
  induction k with
  | zero => simp [schurBinaryWord]
  | succ k ih =>
    rw [pow_succ']
    conv_rhs =>
      rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [schurBinaryWord, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    simp only [← Finset.mul_sum]
    simp only [← ih]
    simp
    exact Matrix.add_mul D U ((D+U)^k)

#print axioms schur_power_binary_word_sum
end SpectralRadiusUpperTail
