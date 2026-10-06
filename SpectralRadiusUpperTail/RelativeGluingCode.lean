import SpectralRadiusUpperTail.OrdinalGluingCount

namespace SpectralRadiusUpperTail
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma finset_pairs_code (E : Finset (A × A)) :
    ∃ code : Fin E.card → A × A, ∀ a b, (∃ k, code k = (a,b)) ↔ (a,b) ∈ E := by
  classical
  let e : E ≃ Fin E.card := Fintype.equivFinOfCardEq (Fintype.card_coe E)
  refine ⟨fun k => (e.symm k).val,?_⟩
  intro a b
  constructor
  · rintro ⟨k,hk⟩
    rw [← hk]
    exact (e.symm k).property
  · intro h
    refine ⟨e ⟨(a,b),h⟩,?_⟩
    simp

/-- Patterns reconstructed from a fixed local relation and d additional pairs
have polynomial count card(A)^(2*d). The local relation need not be counted anew. -/
lemma relative_gluing_pattern_count (Rlocal : A → A → Prop) (d : ℕ) :
    Nat.card {R : Setoid A // ∃ code : Fin d → A × A,
      ∀ x y, R x y ↔ Relation.EqvGen
        (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y} ≤ (Fintype.card A)^(2*d) := by
  classical
  let P := {R : Setoid A // ∃ code : Fin d → A × A,
    ∀ x y, R x y ↔ Relation.EqvGen (fun a b => Rlocal a b ∨ ∃ k, code k = (a,b)) x y}
  let encode : P → (Fin d → A × A) := fun p => Classical.choose p.property
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply Subtype.ext
    apply Setoid.ext
    intro x y
    have hp := Classical.choose_spec p.property x y
    have hq := Classical.choose_spec q.property x y
    change p.val x y ↔ Relation.EqvGen (fun a b => Rlocal a b ∨ ∃ k, encode p k = (a,b)) x y at hp
    change q.val x y ↔ Relation.EqvGen (fun a b => Rlocal a b ∨ ∃ k, encode q k = (a,b)) x y at hq
    rw [hpq] at hp
    exact hp.trans hq.symm
  have h := Fintype.card_le_of_injective encode hinj
  simpa [P, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod,
    ← pow_two, ← pow_mul] using h

#print axioms finset_pairs_code
#print axioms relative_gluing_pattern_count
end SpectralRadiusUpperTail
