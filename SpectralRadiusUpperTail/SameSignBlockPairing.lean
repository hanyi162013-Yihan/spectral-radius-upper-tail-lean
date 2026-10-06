import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- In a constant-sign interval of a noncrossing opposite-sign matching,
no opening can precede a closing. -/
lemma sameSignBlock_no_open_close (f : ℕ → ℕ) (s : ℕ → Bool)
    (hinv : Function.Involutive f) (hopp : ∀ t, s (f t) ≠ s t)
    (hnc : ∀ a b, a < b → b < f a → f a < f b → False)
    (lo hi i j : ℕ) (hlo : lo ≤ i) (hij : i < j) (hhi : j ≤ hi)
    (hblock : ∀ t, lo ≤ t → t ≤ hi → s t = s lo)
    (hopen : i < f i) (hclose : f j < j) : False := by
  have hright : hi < f i := by
    by_contra h
    apply hopp i
    exact (hblock (f i) (by omega) (by omega)).trans
      (hblock i hlo (by omega)).symm
  have hleft : f j < lo := by
    by_contra h
    apply hopp j
    exact (hblock (f j) (by omega) (by omega)).trans
      (hblock j (by omega) hhi).symm
  apply hnc (f j) i (by omega)
  · simpa only [hinv j] using hij
  · simpa only [hinv j] using (show j < f i by omega)

#print axioms sameSignBlock_no_open_close
end SpectralRadiusUpperTail
