import SpectralRadiusUpperTail.DoubleWordPairing

namespace SpectralRadiusUpperTail
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

lemma doubleWord_entry_eq_iff (e : τ → σ) (h : ∀ i, entryMultiplicity e (e i) = 2)
    (i t : τ) : e t = e i ↔ t = i ∨ t = doubleWordPartner e h i := by
  classical
  constructor
  · intro he
    by_cases ht : t = i
    · exact Or.inl ht
    · exact Or.inr ((Classical.choose_spec (doubleWord_unique_partner e h i)).2 t ⟨ht,he⟩)
  · rintro (rfl | ht)
    · rfl
    · rw [ht]
      exact (doubleWordPartner_spec e h i).2

#print axioms doubleWord_entry_eq_iff
end SpectralRadiusUpperTail
