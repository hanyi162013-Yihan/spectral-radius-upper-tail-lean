import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma bool_eq_chain (a b c x y z : Bool) :
    (a = b ↔ x = y) → (b = c ↔ y = z) → (a = c ↔ x = z) := by
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;> decide

/-- Boolean paths with identical change positions determine the same equality
relation on all vertex positions, independently of the initial color. -/
lemma boolPath_eq_iff_of_same_steps {n : ℕ} (c d : Fin (n+1) → Bool)
    (hstep : ∀ i : Fin n, c i.castSucc = c i.succ ↔ d i.castSucc = d i.succ)
    (a b : Fin (n+1)) : c a = c b ↔ d a = d b := by
  have h0 : ∀ i : Fin (n+1), c 0 = c i ↔ d 0 = d i := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih => exact bool_eq_chain _ _ _ _ _ _ ih (hstep i)
  exact bool_eq_chain _ _ _ _ _ _ (by simpa only [eq_comm] using h0 a) (h0 b)

#print axioms bool_eq_chain
#print axioms boolPath_eq_iff_of_same_steps
end SpectralRadiusUpperTail
