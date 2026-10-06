import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The exact arbitrary-dimensional triangular algebra in the soft-tilt coupling.
The field formulation applies to the real and complex cases. -/
namespace SpectralRadiusUpperTail
open Finset
variable {𝕂 : Type*} [Field 𝕂]

lemma inverse_difference (a b w : 𝕂) (ha : a ≠ 0) (hb : b ≠ 0)
    (hw : a-b=w) : w/(a*b)=1/b-1/a := by
  rw [← hw]
  field_simp

lemma telescoping_denominators (d w : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hw : ∀ j, d j-d (j+1)=w j) (n : ℕ) :
    (∑ j ∈ range n, w j/(d j*d (j+1))) = 1/d n-1/d 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, inverse_difference _ _ _ (hd n) (hd (n+1)) (hw n)]
    ring

def weightedPrefix (v x : ℕ → 𝕂) (j : ℕ) : 𝕂 := ∑ k ∈ range j, v k*x k

def triangularForward (v u d x : ℕ → 𝕂) (j : ℕ) : 𝕂 :=
  x j + u j/d j*weightedPrefix v x j

lemma prefix_succ (v x : ℕ → 𝕂) (j : ℕ) :
    weightedPrefix v x (j+1)=weightedPrefix v x j+v j*x j := by
  exact sum_range_succ _ _

lemma scaled_prefix_step (v u d x : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (j : ℕ) :
    weightedPrefix v x (j+1)/d (j+1) = weightedPrefix v x j/d j +
      v j*triangularForward v u d x j/d (j+1) := by
  rw [prefix_succ, triangularForward]
  field_simp [hd j, hd (j+1)]
  linear_combination (weightedPrefix v x j) * hdu j

lemma scaled_prefix_sum (v u d x : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (j : ℕ) :
    weightedPrefix v x j/d j = ∑ k ∈ range j,
      v k*triangularForward v u d x k/d (k+1) := by
  induction j with
  | zero => simp [weightedPrefix]
  | succ j ih =>
    rw [scaled_prefix_step v u d x hd hdu j, ih, sum_range_succ]

/-- Solves the complete triangular system, exposing the d_(k+1) denominator. -/
theorem triangular_inverse (v u d x : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hdu : ∀ j, d j-d (j+1)=v j*u j) (j : ℕ) :
    x j = triangularForward v u d x j - u j *
      ∑ k ∈ range j, v k*triangularForward v u d x k/d (k+1) := by
  rw [← scaled_prefix_sum v u d x hd hdu j]
  unfold triangularForward
  ring

/-- The rank-one mean survives the right transform with denominator d_0. -/
theorem triangular_mean_coefficient (u d w : ℕ → 𝕂) (hd : ∀ j, d j ≠ 0)
    (hw : ∀ j, d j-d (j+1)=w j) (j : ℕ) :
    u j*(1/d j-∑ k ∈ range j, w k/(d k*d (k+1)))=u j/d 0 := by
  rw [telescoping_denominators d w hd hw]
  ring

#print axioms triangular_inverse
#print axioms triangular_mean_coefficient
end SpectralRadiusUpperTail
