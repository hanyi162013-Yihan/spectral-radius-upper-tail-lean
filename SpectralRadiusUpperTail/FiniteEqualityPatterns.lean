import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.BigOperators

namespace SpectralRadiusUpperTail
variable {α : Type*} [Fintype α]

/-- Equality patterns on finitely many positions form a finite type. -/
noncomputable instance equalityPatternFintype : Fintype (Setoid α) := by
  classical
  apply Fintype.ofInjective (fun s : Setoid α => s.r)
  intro r s h
  apply Setoid.ext
  intro a b
  rw [show r.r a b = s.r a b from congrFun (congrFun h a) b]

/-- A crude dimension-independent bound suffices for fixed path length. -/
lemma equalityPattern_card_le : Fintype.card (Setoid α) ≤ 2^(Fintype.card α * Fintype.card α) := by
  classical
  have hi : Function.Injective (fun s : Setoid α => s.r) := by
    intro r s h
    apply Setoid.ext
    intro a b
    rw [show r.r a b = s.r a b from congrFun (congrFun h a) b]
  have h := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_fun, Fintype.card_prop, ← pow_mul] using h

#print axioms equalityPatternFintype
#print axioms equalityPattern_card_le
end SpectralRadiusUpperTail
