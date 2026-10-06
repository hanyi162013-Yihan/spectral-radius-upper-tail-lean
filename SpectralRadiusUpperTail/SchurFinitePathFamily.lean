import SpectralRadiusUpperTail.IncreasingPathGaussianSum
import SpectralRadiusUpperTail.SchurFiniteMomentBudget

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Increasing paths with at most `k` strictly upper-block transitions. -/
abbrev SchurFinitePathFamily (N k : ℕ) :=
  Σ l : Fin (k+1), IncreasingBlockPath N l.val

noncomputable instance (N l : ℕ) : Fintype (IncreasingBlockPath N l) := Fintype.ofFinite _

def schurFinitePath {N k : ℕ} (p : SchurFinitePathFamily N k) : AnyIncreasingPath N :=
  ⟨p.1.val,p.2⟩

lemma schurFinitePath_injective {N k : ℕ} : Function.Injective
    (schurFinitePath : SchurFinitePathFamily N k → AnyIncreasingPath N) := by
  intro p q h
  cases p with
  | mk l p =>
    cases q with
    | mk m q =>
      have hl : l = m := Fin.ext (congrArg Sigma.fst h)
      subst m
      cases h
      rfl

lemma schurFinitePath_length_le {N k : ℕ} (p : SchurFinitePathFamily N k) :
    (schurFinitePath p).1 ≤ k := Nat.lt_succ_iff.mp p.1.isLt

lemma schurFinitePath_sum_by_length {N k : ℕ} (f : ℕ → ℝ) :
    (∑ p : SchurFinitePathFamily N k, f p.1.val) =
      ∑ l : Fin (k+1), (N.choose (l.val+1) : ℝ)*f l.val := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
  have hc : Fintype.card (IncreasingBlockPath N l.val) = N.choose (l.val+1) := by
    rw [← Nat.card_eq_fintype_card]
    exact increasingBlockPath_card N l.val
  simp [hc]

#print axioms schurFinitePath_sum_by_length
end SpectralRadiusUpperTail
