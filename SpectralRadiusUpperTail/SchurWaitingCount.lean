import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Sym.Card

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- Waiting times at the l+1 diagonal blocks of a length-l Schur path.
Their total is k-l because exactly l factors are off diagonal. -/
abbrev SchurWaitingTimes (k l : ℕ) := {d : Fin (l+1) → ℕ // ∑ i, d i = k-l}

/-- Stars and bars supplies the exact binomial factor used before
Cauchy--Schwarz; the hypothesis l<=k excludes nonexistent paths. -/
theorem schurWaitingTimes_card (k l : ℕ) (hlk : l ≤ k) :
    Nat.card (SchurWaitingTimes k l) = k.choose l := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin (l+1)) (k-l))]
  rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hh : l+1+(k-l)-1 = k := by omega
  rw [hh, Nat.choose_symm hlk]

#print axioms schurWaitingTimes_card
end SpectralRadiusUpperTail
