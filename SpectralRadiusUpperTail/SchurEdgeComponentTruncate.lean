import SpectralRadiusUpperTail.SchurEdgeComponents
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- If exactly `l+1` bridges occur in `k` factors, the first diagonal
waiting time is at most `k-l-1`. The other terms vanish identically. -/
theorem noncommEdgeComponent_succ_truncate {R : Type*} [Semiring R]
    (D U : R) (l k : ℕ) (hlk : l < k) :
    noncommEdgeComponent D U (l+1) k =
      ∑ s ∈ Finset.range (k-l),
        D^s * U * noncommEdgeComponent D U l (k-s-1) := by
  rw [noncommEdgeComponent]
  have hsub : Finset.range (k-l) ⊆ Finset.range k :=
    Finset.range_mono (by omega)
  apply (Finset.sum_subset hsub ?_).symm
  intro s hs hnot
  have hsk : k-s-1 < l := by
    have hs' := Finset.mem_range.mp hs
    have hn' := Finset.mem_range.not.mp hnot
    omega
  rw [noncommEdgeComponent_zero_of_length_gt D U l (k-s-1) hsk, mul_zero]

#print axioms noncommEdgeComponent_succ_truncate
end SpectralRadiusUpperTail
