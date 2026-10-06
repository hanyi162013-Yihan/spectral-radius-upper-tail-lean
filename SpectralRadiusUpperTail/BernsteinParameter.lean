import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail

/-- An explicit admissible exponential parameter and its Bernstein exponent. -/
lemma bernstein_parameter {v t : ℝ} (hv : 0 ≤ v) (ht : 0 < t) :
    let s := t/(4*v+2*t)
    0 ≤ s ∧ s ≤ 1/2 ∧ -s*t+2*s^2*v ≤ -t^2/(8*v+4*t) := by
  let s := t/(4*v+2*t)
  have hd : 0 < 4*v+2*t := by positivity
  have hs : 0 ≤ s := div_nonneg ht.le hd.le
  have hs1 : s ≤ 1/2 := (div_le_iff₀ hd).2 (by linarith)
  have he : s*(4*v+2*t) = t := div_mul_cancel₀ _ hd.ne'
  have hb : 4*s*v ≤ t := by nlinarith [mul_nonneg hs ht.le]
  have hh : -s*t+2*s^2*v ≤ -(s*t)/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hb hs]
  have heq : s*t/2 = t^2/(8*v+4*t) := by
    dsimp [s]
    have hd2 : 8*v+4*t ≠ 0 := by positivity
    field_simp
    <;> ring
  refine ⟨hs, hs1, ?_⟩
  calc
    _ ≤ -(s*t)/2 := hh
    _ = -t^2/(8*v+4*t) := by rw [neg_div, heq, neg_div]

#print axioms bernstein_parameter
end SpectralRadiusUpperTail
