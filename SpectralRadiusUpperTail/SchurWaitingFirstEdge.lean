import SpectralRadiusUpperTail.SchurWaitingConsEquiv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- For a path with `l+1` upper edges, the first waiting time and the
remaining `l`-edge waiting allocation determine one another exactly. -/
noncomputable def schurWaitingFirstEdgeEquiv (k l : ℕ) (hlk : l < k) :
    SchurWaitingTimes k (l+1) ≃
      Σ s : Fin (k-l), SchurWaitingTimes (k-s.val-1) l where
  toFun m := by
    have hsum : m.val 0 + ∑ j : Fin (l+1), m.val j.succ = k-(l+1) := by
      simpa only [Fin.sum_univ_succ] using m.property
    have hs : m.val 0 < k-l := by omega
    refine ⟨⟨m.val 0, hs⟩, ⟨Fin.tail m.val, ?_⟩⟩
    dsimp [Fin.tail]
    omega
  invFun p := by
    refine ⟨Fin.cons p.1.val p.2.val, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hs := p.1.isLt
    have ht := p.2.property
    omega
  left_inv m := by
    apply Subtype.ext
    exact Fin.cons_self_tail m.val
  right_inv p := by
    cases p with
    | mk s t => rfl

#print axioms schurWaitingFirstEdgeEquiv
end SpectralRadiusUpperTail
