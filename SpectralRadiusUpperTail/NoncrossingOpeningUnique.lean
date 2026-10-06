import SpectralRadiusUpperTail.NoncrossingPartnerOrder

namespace SpectralRadiusUpperTail

/-- A finite noncrossing perfect matching is uniquely determined by its opening positions. -/
lemma noncrossing_matching_eq_of_openings {n : ℕ} (f g : Fin n → Fin n)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfixf : ∀ i, f i ≠ i) (hfixg : ∀ i, g i ≠ i)
    (hncf : ∀ a b, a < b → b < f a → f a < f b → False)
    (hncg : ∀ a b, a < b → b < g a → g a < g b → False)
    (hopen : ∀ i, i < f i ↔ i < g i) : f = g := by
  have hclose : ∀ k : ℕ, ∀ j : Fin n, j.val = k → f j < j → f j = g j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj hfj
      have hgj : g j < j := by
        have ho := hopen j
        have hn := hfixg j
        omega
      have hp : ∀ t, t < j → f t < t → f t = g t := by
        intro t ht hft
        exact ih t.val (by omega) t rfl hft
      have hp' : ∀ t, t < j → g t < t → g t = f t := by
        intro t ht hgt
        have hft : f t < t := by
          have ho := hopen t
          have hn := hfixf t
          omega
        exact (hp t ht hft).symm
      have hfg := noncrossing_closing_partner_not_lt f g hf hg hncf hopen j hgj hp
      have hgf := noncrossing_closing_partner_not_lt g f hg hf hncg
        (fun t => (hopen t).symm) j hfj hp'
      exact le_antisymm (not_lt.mp hgf) (not_lt.mp hfg)
  have hc : ∀ j, f j < j → f j = g j := fun j => hclose j.val j rfl
  funext i
  by_cases hi : f i < i
  · exact hc i hi
  · have hop : i < f i := by
      have hn := hfixf i
      omega
    have hcl : f (f i) < f i := by simpa only [hf i] using hop
    have he := hc (f i) hcl
    have hh := congrArg g he
    simpa only [hf i, hg (f i)] using hh.symm

#print axioms noncrossing_matching_eq_of_openings
end SpectralRadiusUpperTail
