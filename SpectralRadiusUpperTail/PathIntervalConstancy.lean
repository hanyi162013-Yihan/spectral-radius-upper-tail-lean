import Mathlib.Tactic

namespace SpectralRadiusUpperTail
variable {α : Type*}

lemma path_constant_on_interval (p : ℕ → α) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ t, a ≤ t → t < b → p (t+1) = p t) : p b = p a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [hstep b hab (Nat.lt_succ_self b)]
    apply ih
    intro t hat htb
    exact hstep t hat (Nat.lt_trans htb (Nat.lt_succ_self b))

#print axioms path_constant_on_interval
end SpectralRadiusUpperTail
