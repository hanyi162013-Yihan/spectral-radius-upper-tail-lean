import SpectralRadiusUpperTail.SchurNoncommDuhamel
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The part of `(D+U)^k` containing exactly `l` occurrences of `U`,
organized by the waiting time before its first occurrence. -/
noncomputable def noncommEdgeComponent {R : Type*} [Semiring R] (D U : R) :
    ℕ → ℕ → R
  | 0, k => D^k
  | l+1, k => ∑ s ∈ Finset.range k,
      D^s * U * noncommEdgeComponent D U l (k-s-1)

lemma noncommEdgeComponent_zero_of_length_gt {R : Type*} [Semiring R]
    (D U : R) (l k : ℕ) (hk : k < l) :
    noncommEdgeComponent D U l k = 0 := by
  induction l generalizing k with
  | zero => omega
  | succ l ih =>
    rw [noncommEdgeComponent]
    apply Finset.sum_eq_zero
    intro s hs
    have hsk : k-s-1 < l := by
      have hmem := Finset.mem_range.mp hs
      omega
    rw [ih (k-s-1) hsk, mul_zero]

#print axioms noncommEdgeComponent_zero_of_length_gt
end SpectralRadiusUpperTail
