import SpectralRadiusUpperTail.EntrySupportExcess

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

/-- Counting selected word positions by the multiplicities of their entries. -/
lemma entryMultiplicity_filter_card (e : τ → σ) (P : σ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t => P (e t))).card =
      ∑ i : σ, if P i then entryMultiplicity e i else 0 := by
  classical
  simp only [entryMultiplicity_indicator_sum, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  have hdis : ∀ i : σ,
      (if P i then ∑ t : τ, if e t = i then 1 else 0 else 0) =
        ∑ t : τ, if e t = i then (if P i then 1 else 0) else 0 := by
    intro i
    by_cases hi : P i <;> simp [hi]
  simp_rw [hdis]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : P (e t) <;> simp [h]

/-- Erase high-multiplicity entries and entries outside a chosen support subset.
Only twice-occurring entries remain; the erased mass has a defect-sized bound. -/
lemma entryPruning_card_le (e : τ → σ) (T : Finset σ)
    (hT : T ⊆ Finset.univ.image e) (hno : ∀ i, entryMultiplicity e i ≠ 1) :
    (Finset.univ.filter (fun t => entryMultiplicity e (e t) ≠ 2 ∨ e t ∉ T)).card ≤
      3 * ∑ i : σ, (entryMultiplicity e i - 2) +
        2 * ((Finset.univ.image e).card - T.card) := by
  classical
  rw [entryMultiplicity_filter_card e (fun i => entryMultiplicity e i ≠ 2 ∨ i ∉ T)]
  have hp : ∀ i : σ,
      (if entryMultiplicity e i ≠ 2 ∨ i ∉ T then entryMultiplicity e i else 0) ≤
        (if 3 ≤ entryMultiplicity e i then entryMultiplicity e i else 0) +
          (if i ∈ (Finset.univ.image e) \ T then 2 else 0) := by
    intro i
    have hn := hno i
    have hu : i ∈ Finset.univ.image e ↔ 0 < entryMultiplicity e i := by
      simp [entryMultiplicity_pos_iff]
    simp only [Finset.mem_sdiff,hu]
    by_cases hi : i ∈ T <;> simp only [hi,not_true_eq_false,not_false_eq_true,or_false,or_true,and_true,and_false,ite_false,ite_true]
    all_goals split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  rw [Finset.sum_add_distrib] at hs
  have hc : (∑ i : σ, if i ∈ (Finset.univ.image e) \ T then 2 else 0) =
      2 * ((Finset.univ.image e).card - T.card) := by
    rw [← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_sdiff_of_subset hT]
    omega
  rw [hc] at hs
  exact hs.trans (Nat.add_le_add_right (highMultiplicity_mass_le _) _)

/-- Numerical accounting for the tree-support pruning step. -/
lemma entryPruning_defect_budget (r E V δ D : ℕ)
    (hlen : 2*r = 2*E+δ) (hv : V ≤ E+1) (hV : 1 ≤ V)
    (hD : D ≤ 3*δ + 2*(E-(V-1))) : D ≤ 8*(r+1-V) := by
  omega

#print axioms entryMultiplicity_filter_card
#print axioms entryPruning_card_le
#print axioms entryPruning_defect_budget
end SpectralRadiusUpperTail
