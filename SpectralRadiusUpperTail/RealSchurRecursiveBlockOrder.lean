import SpectralRadiusUpperTail.RealSchurRecursiveMixedIndex
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The ordinal number of a coordinate's block in a recursive block list. -/
def realSchurRecursiveBlockNumber :
    (s : List ℕ) → RealSchurRecursiveBlockIndex s → ℕ
  | [], x => x.elim
  | _ :: _, Sum.inl _ => 0
  | _ :: ks, Sum.inr x =>
      realSchurRecursiveBlockNumber ks x + 1

/-- Recursive block-upper-triangularity kills every entry below the
diagonal in block order, including entries more than one block away. -/
theorem realSchurRecursiveBlockUpper_lower_zero
    (s : List ℕ)
    (A : Matrix (RealSchurRecursiveBlockIndex s)
      (RealSchurRecursiveBlockIndex s) ℝ)
    (hA : RealSchurRecursiveBlockUpper s A)
    (i j : RealSchurRecursiveBlockIndex s)
    (hij : realSchurRecursiveBlockNumber s j <
      realSchurRecursiveBlockNumber s i) : A i j = 0 := by
  induction s with
  | nil => exact i.elim
  | cons k ks ih =>
      change (∀ i : RealSchurRecursiveBlockIndex ks,
        ∀ j : Fin k, A (Sum.inr i) (Sum.inl j) = 0) ∧
        RealSchurRecursiveBlockUpper ks (A.submatrix Sum.inr Sum.inr) at hA
      rcases hA with ⟨hfirst, htail⟩
      cases i with
      | inl ii =>
          cases j with
          | inl jj => simp [realSchurRecursiveBlockNumber] at hij
          | inr jj => simp [realSchurRecursiveBlockNumber] at hij
      | inr ii =>
          cases j with
          | inl jj => exact hfirst ii jj
          | inr jj =>
              have hlt : realSchurRecursiveBlockNumber ks jj <
                  realSchurRecursiveBlockNumber ks ii := by
                simpa [realSchurRecursiveBlockNumber] using hij
              exact ih (A.submatrix Sum.inr Sum.inr) htail ii jj hlt

/-- The explicit recursive-to-mixed coordinate equivalence preserves the
block number. -/
theorem realSchurRecursiveMixedIndexEquiv_blockNumber
    (s : List ℕ) (x : RealSchurRecursiveBlockIndex s) :
    (realSchurRecursiveMixedIndexEquiv s x).1.val =
      realSchurRecursiveBlockNumber s x := by
  induction s with
  | nil => exact x.elim
  | cons k ks ih =>
      cases x with
      | inl j => rfl
      | inr y =>
          change (realSchurRecursiveMixedIndexEquiv ks y).1.val + 1 =
            realSchurRecursiveBlockNumber ks y + 1
          exact congrArg (· + 1) (ih y)

#print axioms realSchurRecursiveBlockUpper_lower_zero
#print axioms realSchurRecursiveMixedIndexEquiv_blockNumber
end SpectralRadiusUpperTail
