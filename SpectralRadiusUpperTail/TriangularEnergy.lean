import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open Finset

def lowerPairSum (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, w i * ∑ j ∈ range i, w j

lemma square_sum_decomposition (w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, w i)^2 =
      (∑ i ∈ range n, (w i)^2) + 2*lowerPairSum w n := by
  induction n with
  | zero => simp [lowerPairSum]
  | succ n ih =>
    unfold lowerPairSum at *
    simp only [sum_range_succ]
    nlinarith [ih]

theorem lowerPairSum_le_half (w : ℕ → ℝ) (n : ℕ)
    (hnorm : ∑ i ∈ range n, w i = 1) : lowerPairSum w n ≤ 1/2 := by
  have h := square_sum_decomposition w n
  have hsq : 0 ≤ ∑ i ∈ range n, (w i)^2 := sum_nonneg (fun i _ => sq_nonneg (w i))
  rw [hnorm] at h
  nlinarith

/-- The complete scalar sum underlying the Hilbert--Schmidt estimate for T-I. -/
theorem triangular_energy_le (w d : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (ha : 0 < a) (hd : ∀ i, a ≤ d i)
    (hnorm : ∑ i ∈ range n, w i = 1) :
    (∑ i ∈ range n, ∑ j ∈ range i, w i*w j/(d j)^2) ≤ 1/(2*a^2) := by
  have hden (j : ℕ) : a^2 ≤ (d j)^2 := by
    have hj := hd j
    nlinarith
  have hsum : (∑ i ∈ range n, ∑ j ∈ range i, w i*w j/(d j)^2) ≤
      ∑ i ∈ range n, ∑ j ∈ range i, w i*w j/a^2 := by
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    exact div_le_div_of_nonneg_left (mul_nonneg (hw i) (hw j))
      (sq_pos_of_pos ha) (hden j)
  have hid : (∑ i ∈ range n, ∑ j ∈ range i, w i*w j/a^2) =
      lowerPairSum w n/a^2 := by
    simp only [lowerPairSum, sum_div, mul_sum]
  rw [hid] at hsum
  calc
    (∑ i ∈ range n, ∑ j ∈ range i, w i*w j/(d j)^2) ≤ lowerPairSum w n/a^2 := hsum
    _ ≤ (1/2)/a^2 := div_le_div_of_nonneg_right (lowerPairSum_le_half w n hnorm) (sq_nonneg a)
    _ = 1/(2*a^2) := by ring

#print axioms square_sum_decomposition
#print axioms triangular_energy_le
end SpectralRadiusUpperTail
