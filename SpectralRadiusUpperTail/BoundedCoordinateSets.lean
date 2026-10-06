import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

noncomputable def boundedCoordinateSets (n M : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.range (M+1)).biUnion (fun m => Finset.univ.powersetCard m)

lemma mem_boundedCoordinateSets {n M : ℕ} (I : Finset (Fin n)) :
    I ∈ boundedCoordinateSets n M ↔ I.card ≤ M := by
  simp only [boundedCoordinateSets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨m, hm, he⟩
    omega
  · intro h
    exact ⟨I.card, by omega, rfl⟩

lemma boundedCoordinateSets_card (n M : ℕ) :
    (boundedCoordinateSets n M).card ≤ (M+1)*(n+1)^M := by
  apply (Finset.card_biUnion_le).trans
  calc
    _ = ∑ m ∈ Finset.range (M+1), n.choose m := by simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∑ _m ∈ Finset.range (M+1), (n+1)^M := by
      apply Finset.sum_le_sum
      intro m hm
      exact (Nat.choose_le_pow n m).trans ((Nat.pow_le_pow_left (by omega : n ≤ n+1) m).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ n+1) (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hm)))
    _ = _ := by simp

#print axioms boundedCoordinateSets
#print axioms mem_boundedCoordinateSets
#print axioms boundedCoordinateSets_card
end SpectralRadiusUpperTail
