import SpectralRadiusUpperTail.SchurBlockDuhamel
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A first-jump recursive path expansion. At each step, `s` diagonal
factors precede the first off-diagonal factor. This representation does
not require commutativity of the block coefficients. -/
noncomputable def schurRecursivePathSum {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (k : ℕ) (i j : ι) : R :=
  match k with
  | 0 => if i = j then 1 else 0
  | k+1 =>
      (if i = j then (D i)^(k+1) else 0) +
        ∑ s ∈ Finset.range (k+1), ∑ h : ι,
          (D i)^s * U i h * schurRecursivePathSum D U (k-s) h j
termination_by k
decreasing_by omega

/-- The recursive first-jump sum is exactly the matrix-power entry. -/
theorem schur_recursive_path_sum_eq_power {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (D : ι → R) (U : Matrix ι ι R) (k : ℕ) :
    ∀ i j : ι, schurRecursivePathSum D U k i j =
      ((Matrix.diagonal D + U)^k) i j := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro i j
    cases k with
    | zero => simp [schurRecursivePathSum, Matrix.one_apply]
    | succ k =>
      rw [schurRecursivePathSum, diagonal_plus_upper_power_entry]
      apply congrArg (fun x : R => (if i = j then (D i)^(k+1) else 0) + x)
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro h _
      have he : k+1-s-1 = k-s := by omega
      rw [he]
      have hlt : k-s < k+1 := by omega
      rw [ih (k-s) hlt h j]

#print axioms schur_recursive_path_sum_eq_power
end SpectralRadiusUpperTail
