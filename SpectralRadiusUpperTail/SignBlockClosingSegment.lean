import SpectralRadiusUpperTail.FiniteSameSignBlockPairing
import SpectralRadiusUpperTail.InitialSegmentCard

namespace SpectralRadiusUpperTail

lemma signBlock_closings_lower {n m : ℕ} (f : Fin n → Fin n) (s : Fin n → Bool)
    (hinv : Function.Involutive f) (hopp : ∀ t, s (f t) ≠ s t)
    (hnc : ∀ a b, a < b → b < f a → f a < f b → False)
    (lo hi : Fin n) (v : Fin m → Fin n) (hv : StrictMono v)
    (hbounds : ∀ t, lo ≤ v t ∧ v t ≤ hi)
    (hblock : ∀ t, lo ≤ t → t ≤ hi → s t = s lo) :
    IsLowerSet {t : Fin m | f (v t) < v t} := by
  intro j i hij hj
  change f (v i) < v i
  change f (v j) < v j at hj
  rcases lt_or_eq_of_le hij with hlt | heq
  · by_contra hn
    have hne : f (v i) ≠ v i := by
      intro he
      exact hopp (v i) (congrArg s he)
    have hop : v i < f (v i) := by omega
    exact finiteSameSignBlock_no_open_close f s hinv hopp hnc lo hi (v i) (v j)
      (hbounds i).1 (hv hlt) (hbounds j).2 hblock hop hj
  · simpa only [heq] using hj

#print axioms signBlock_closings_lower
end SpectralRadiusUpperTail
