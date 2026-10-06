import SpectralRadiusUpperTail.DoubleWordPartnerFiber

namespace SpectralRadiusUpperTail
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

lemma doubleWord_entry_eq_iff_matching (e : τ → σ)
    (h : ∀ i, entryMultiplicity e (e i) = 2) (f : τ → τ)
    (hfix : ∀ i, f i ≠ i) (he : ∀ i, e (f i) = e i) (i j : τ) :
    e j = e i ↔ j = i ∨ j = f i := by
  have hf : f i = doubleWordPartner e h i :=
    ((doubleWord_entry_eq_iff e h i (f i)).mp (he i)).resolve_left (hfix i)
  rw [doubleWord_entry_eq_iff e h i j, ← hf]

#print axioms doubleWord_entry_eq_iff_matching
end SpectralRadiusUpperTail
