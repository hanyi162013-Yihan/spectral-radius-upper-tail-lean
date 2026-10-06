import SpectralRadiusUpperTail.FiniteSameSignBlockPairing
import Mathlib.Order.UpperLower.Basic

namespace SpectralRadiusUpperTail

lemma convexSignBlock_closings_lower {n m : ℕ} (f : Fin n → Fin n) (s : Fin n → Bool)
    (hinv : Function.Involutive f) (hopp : ∀ t, s (f t) ≠ s t)
    (hnc : ∀ a b, a < b → b < f a → f a < f b → False)
    (v : Fin m → Fin n) (hv : StrictMono v)
    (hconv : ∀ i j t, v i ≤ t → t ≤ v j → ∃ k, v k = t)
    (hs : ∀ i j, s (v i) = s (v j)) :
    IsLowerSet {t : Fin m | f (v t) < v t} := by
  intro j i hij hj
  change f (v i) < v i
  change f (v j) < v j at hj
  rcases lt_or_eq_of_le hij with hlt | heq
  · by_contra hn
    have hne : f (v i) ≠ v i := fun he => hopp (v i) (congrArg s he)
    have hop : v i < f (v i) := by omega
    apply finiteSameSignBlock_no_open_close f s hinv hopp hnc (v i) (v j) (v i) (v j)
      le_rfl (hv hlt) le_rfl _ hop hj
    intro t hit htj
    obtain ⟨k,rfl⟩ := hconv i j t hit htj
    exact hs k i
  · simpa only [heq] using hj

#print axioms convexSignBlock_closings_lower
end SpectralRadiusUpperTail
