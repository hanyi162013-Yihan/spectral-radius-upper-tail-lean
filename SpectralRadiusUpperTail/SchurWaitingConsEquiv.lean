import SpectralRadiusUpperTail.SchurWaitingCount
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

abbrev SchurComposition (l m : ℕ) :=
  {d : Fin (l+1) → ℕ // ∑ i, d i = m}

/-- A waiting-time composition splits into its first wait and the
remaining composition. -/
noncomputable def schurCompositionConsEquiv (l m : ℕ) :
    SchurComposition (l+1) m ≃
      Σ s : Fin (m+1), SchurComposition l (m-s.val) where
  toFun d := by
    have hsum : d.val 0 + ∑ i : Fin (l+1), d.val i.succ = m := by
      simpa only [Fin.sum_univ_succ] using d.property
    have hs : d.val 0 ≤ m := by omega
    refine ⟨⟨d.val 0, Nat.lt_succ_of_le hs⟩, ⟨Fin.tail d.val, ?_⟩⟩
    dsimp [Fin.tail]
    omega
  invFun p := by
    refine ⟨Fin.cons p.1.val p.2.val, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hs : p.1.val ≤ m := Nat.le_of_lt_succ p.1.isLt
    have ht := p.2.property
    omega
  left_inv d := by
    apply Subtype.ext
    exact Fin.cons_self_tail d.val
  right_inv p := by
    cases p with
    | mk s t => rfl

#print axioms schurCompositionConsEquiv
end SpectralRadiusUpperTail
