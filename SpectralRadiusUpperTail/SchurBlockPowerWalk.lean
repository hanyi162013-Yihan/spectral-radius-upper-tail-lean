import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators
open Classical

/-- The ordered contribution of a length-`k` walk to one entry of a
matrix power. This works for noncommutative coefficients, including
the `2 × 2` real matrices used as Schur blocks. -/
def blockPowerWalk {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    (A : Matrix ι ι R) : (k : ℕ) → ι → ι → (Fin k → ι) → R
  | 0, i, j, _ => if i = j then 1 else 0
  | k+1, i, j, v => A i (v 0) * blockPowerWalk A k (v 0) j (fun a => v a.succ)

/-- Exact entrywise walk expansion of a matrix power. -/
theorem block_power_walk_sum {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Semiring R] (A : Matrix ι ι R) (k : ℕ) (i j : ι) :
    (A^k) i j = ∑ v : Fin k → ι, blockPowerWalk A k i j v := by
  induction k generalizing i with
  | zero => simp [blockPowerWalk, Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    conv_rhs =>
      rw [← (Fin.consEquiv (fun _ : Fin (k+1) => ι)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [blockPowerWalk, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    simp only [← Finset.mul_sum, ← ih]

/-- A walk that never descends in block index, including its final step. -/
def blockWalkWeakIncreasing {ι : Type*} [LE ι] :
    (k : ℕ) → ι → ι → (Fin k → ι) → Prop
  | 0, i, j, _ => i = j
  | k+1, i, j, v => i ≤ v 0 ∧
      blockWalkWeakIncreasing k (v 0) j (fun a => v a.succ)

/-- Every downward step in an upper-triangular block matrix kills its walk. -/
theorem block_power_walk_zero_of_descending {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    (A : Matrix ι ι R) (hA : ∀ i j, j < i → A i j = 0)
    (k : ℕ) (i j : ι) (v : Fin k → ι)
    (h : ¬ blockWalkWeakIncreasing k i j v) :
    blockPowerWalk A k i j v = 0 := by
  induction k generalizing i j with
  | zero =>
    simp only [blockWalkWeakIncreasing] at h
    simp [blockPowerWalk, h]
  | succ k ih =>
    by_cases hle : i ≤ v 0
    · have ht : ¬ blockWalkWeakIncreasing k (v 0) j (fun a => v a.succ) := by
        intro ht
        exact h ⟨hle, ht⟩
      simp only [blockPowerWalk, ih (v 0) j _ ht, mul_zero]
    · have hlt : v 0 < i := lt_of_not_ge hle
      simp only [blockPowerWalk, hA i (v 0) hlt, zero_mul]

/-- Exact matrix-power expansion restricted to nondecreasing block walks. -/
theorem upper_block_power_weak_walk_sum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Semiring R]
    (A : Matrix ι ι R) (hA : ∀ i j, j < i → A i j = 0)
    (k : ℕ) (i j : ι) :
    (A^k) i j = ∑ v : Fin k → ι,
      if blockWalkWeakIncreasing k i j v then blockPowerWalk A k i j v else 0 := by
  classical
  rw [block_power_walk_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : blockWalkWeakIncreasing k i j v
  · simp only [if_pos hv]
  · simp only [if_neg hv, block_power_walk_zero_of_descending A hA k i j v hv]

#print axioms block_power_walk_sum
#print axioms upper_block_power_weak_walk_sum
end SpectralRadiusUpperTail
