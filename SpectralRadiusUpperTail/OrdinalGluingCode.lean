import SpectralRadiusUpperTail.FiniteFiberGluing
import SpectralRadiusUpperTail.FiniteEqualityPatterns
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Quotient
import Mathlib.SetTheory.Cardinal.Finite

namespace SpectralRadiusUpperTail

/-- Every equality pattern on N ordinal slots can be reconstructed from
exactly N minus its number of classes many ordinal pairs. No ambient vertex
labels occur in the code. This does not yet bound the deficit of actual tours. -/
lemma exists_ordinal_gluing_code (N : ℕ) (R : Setoid (Fin N)) :
    ∃ code : Fin (N - Nat.card (Quotient R)) → Fin N × Fin N,
      ∀ x y, Relation.EqvGen (fun a b => ∃ k, code k = (a,b)) x y ↔ R x y := by
  classical
  let : Fintype (Quotient R) := Fintype.ofFinite _
  obtain ⟨E, hcard, hE⟩ := exists_finite_fiber_gluing
    (Quotient.mk R) (fun q => Quotient.inductionOn q (fun a => ⟨a, rfl⟩))
  have hc : Fintype.card E = N - Nat.card (Quotient R) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, Nat.card_eq_fintype_card] using hcard
  let e : E ≃ Fin (N - Nat.card (Quotient R)) := Fintype.equivFinOfCardEq hc
  let code : Fin (N - Nat.card (Quotient R)) → Fin N × Fin N :=
    fun k => (e.symm k).val
  have hr : (fun a b => ∃ k, code k = (a,b)) = (fun a b => (a,b) ∈ E) := by
    funext a b
    apply propext
    constructor
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact (e.symm k).property
    · intro h
      refine ⟨e ⟨(a,b),h⟩, ?_⟩
      simp [code]
  refine ⟨code, ?_⟩
  intro x y
  rw [hr, hE]
  exact Quotient.eq

#print axioms exists_ordinal_gluing_code
end SpectralRadiusUpperTail
