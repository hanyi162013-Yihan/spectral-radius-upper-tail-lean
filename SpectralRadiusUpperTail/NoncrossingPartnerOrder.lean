import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Once earlier closing partners agree, two noncrossing matchings with the same
opening positions cannot choose ordered distinct partners at the current closing. -/
lemma noncrossing_closing_partner_not_lt {n : ℕ} (f g : Fin n → Fin n)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hnc : ∀ a b, a < b → b < f a → f a < f b → False)
    (hopen : ∀ i, i < f i ↔ i < g i) (j : Fin n)
    (hgj : g j < j)
    (hprev : ∀ t, t < j → f t < t → f t = g t) : ¬ f j < g j := by
  intro hlt
  have hb : g j < f (g j) := (hopen (g j)).mpr (by simpa only [hg j] using hgj)
  have hbefore : ¬ f (g j) < j := by
    intro hbj
    have hclose : f (f (g j)) < f (g j) := by simpa only [hf (g j)] using hb
    have he := hprev (f (g j)) hbj hclose
    have hge : g (f (g j)) = g j := by rw [← he, hf (g j)]
    have heq := congrArg g hge
    simp only [hg (f (g j)), hg j] at heq
    omega
  have hne : f (g j) ≠ j := by
    intro he
    have he' := congrArg f he
    simp only [hf (g j)] at he'
    omega
  have hafter : j < f (g j) := by omega
  apply hnc (f j) (g j) hlt
  · simpa only [hf j] using hgj
  · simpa only [hf j] using hafter

#print axioms noncrossing_closing_partner_not_lt
end SpectralRadiusUpperTail
