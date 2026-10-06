import SpectralRadiusUpperTail.BoundedGluingCount

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma finset_exists_enumeration (E : Finset A) :
    ∃ f : Fin E.card → A, Finset.univ.image f = E := by
  classical
  let e : E ≃ Fin E.card := Fintype.equivFinOfCardEq (Fintype.card_coe E)
  refine ⟨fun i => (e.symm i).val,?_⟩
  ext a
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    exact (e.symm i).property
  · intro ha
    refine Finset.mem_image.mpr ⟨e ⟨a,ha⟩,Finset.mem_univ _,?_⟩
    simp

lemma fixed_card_finset_count (d : ℕ) :
    Nat.card {E : Finset A // E.card = d} ≤ (Fintype.card A)^d := by
  classical
  let P := {E : Finset A // E.card = d}
  have hex (E : P) : ∃ f : Fin d → A, Finset.univ.image f = E.val := by
    rcases E with ⟨E,hE⟩
    cases hE
    exact finset_exists_enumeration E
  let encode : P → (Fin d → A) := fun E => Classical.choose (hex E)
  have hinj : Function.Injective encode := by
    intro E F h
    apply Subtype.ext
    exact (Classical.choose_spec (hex E)).symm.trans
      ((congrArg (fun f : Fin d → A => Finset.univ.image f) h).trans (Classical.choose_spec (hex F)))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective encode hinj

lemma bounded_card_finset_count (b : ℕ) :
    Nat.card {E : Finset A // E.card ≤ b} ≤ (b+1)*(max 1 (Fintype.card A))^b := by
  classical
  let P := {E : Finset A // E.card ≤ b}
  let encode : P → Σ d : Fin (b+1), {E : Finset A // E.card = d.val} := fun E =>
    ⟨⟨E.val.card,Nat.lt_succ_of_le E.property⟩,⟨E.val,rfl⟩⟩
  have hinj : Function.Injective encode := by
    intro E F h
    exact Subtype.ext (congrArg (fun z : Σ d : Fin (b+1), {E : Finset A // E.card = d.val} =>
      z.2.val) h)
  have h : Nat.card P ≤ ∑ d : Fin (b+1), Nat.card {E : Finset A // E.card = d.val} := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using
      Fintype.card_le_of_injective encode hinj
  calc
    Nat.card P ≤ ∑ d : Fin (b+1), Nat.card {E : Finset A // E.card = d.val} := h
    _ ≤ ∑ d : Fin (b+1), (Fintype.card A)^d.val :=
      Finset.sum_le_sum (fun d _ => fixed_card_finset_count d.val)
    _ ≤ ∑ _d : Fin (b+1), (max 1 (Fintype.card A))^b := by
      apply Finset.sum_le_sum
      intro d _
      exact (Nat.pow_le_pow_left (le_max_right 1 (Fintype.card A)) d.val).trans
        (Nat.pow_le_pow_right (le_max_left 1 (Fintype.card A)) (Nat.le_of_lt_succ d.isLt))
    _ = _ := by simp

#print axioms finset_exists_enumeration
#print axioms fixed_card_finset_count
#print axioms bounded_card_finset_count
end SpectralRadiusUpperTail
