import SpectralRadiusUpperTail.OrdinalGluingCode

namespace SpectralRadiusUpperTail

/-- Equality patterns of deficit d on N slots admit at most N^(2*d)
codes. In applications the slot domain must first be the disjoint union
of local vertex quotients, not the whole unquotiented path. -/
lemma ordinal_gluing_pattern_count (N d : ℕ) :
    Nat.card {R : Setoid (Fin N) // N - Nat.card (Quotient R) = d} ≤ N^(2*d) := by
  classical
  let P := {R : Setoid (Fin N) // N - Nat.card (Quotient R) = d}
  have hex : ∀ p : P, ∃ code : Fin d → Fin N × Fin N,
      ∀ x y, Relation.EqvGen (fun a b => ∃ k, code k = (a,b)) x y ↔ p.val x y := by
    intro p
    have h := exists_ordinal_gluing_code N p.val
    rw [p.property] at h
    exact h
  let encode : P → (Fin d → Fin N × Fin N) := fun p => Classical.choose (hex p)
  have hinj : Function.Injective encode := by
    intro p q hpq
    apply Subtype.ext
    apply Setoid.ext
    intro x y
    have hp := Classical.choose_spec (hex p) x y
    have hq := Classical.choose_spec (hex q) x y
    change Relation.EqvGen (fun a b => ∃ k, encode p k = (a,b)) x y ↔ p.val x y at hp
    change Relation.EqvGen (fun a b => ∃ k, encode q k = (a,b)) x y ↔ q.val x y at hq
    rw [hpq] at hp
    exact hp.symm.trans hq
  have h := Fintype.card_le_of_injective encode hinj
  simpa [P, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_prod,
    ← pow_two, ← pow_mul] using h

#print axioms ordinal_gluing_pattern_count
end SpectralRadiusUpperTail
