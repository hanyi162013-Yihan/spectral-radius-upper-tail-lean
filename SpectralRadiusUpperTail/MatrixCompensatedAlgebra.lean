import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

namespace SpectralRadiusUpperTail

/-- Both orders of the noncommutative cross term are retained. -/
lemma compensated_noncommutative_square {A : Type*} [Ring A] [Algebra ℝ A]
    (s : ℝ) (X D : A) :
    (s • X - (2*s^2) • D)^2 =
      s^2 • X^2 - (2*s^3) • (X*D+D*X) + (4*s^4) • D^2 := by
  simp only [pow_two, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add]
  module

/-- The compensated increment stays within the unit norm ball at the
parameter range used by the exponential supermartingale argument. -/
lemma compensated_increment_norm_le_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (s : ℝ) (X D : A) (hs : 0 ≤ s) (hs1 : s ≤ 1/2)
    (hX : ‖X‖ ≤ 1) (hD : ‖D‖ ≤ 1) :
    ‖s • X - (2*s^2) • D‖ ≤ 1 := by
  have hs2 : 0 ≤ 2*s^2 := by positivity
  calc
    _ ≤ ‖s • X‖+‖(2*s^2) • D‖ := norm_sub_le _ _
    _ = s*‖X‖+(2*s^2)*‖D‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg hs2]
    _ ≤ s+2*s^2 := by nlinarith
    _ ≤ 1 := by nlinarith [sq_nonneg (s-1/2)]

#print axioms compensated_noncommutative_square
#print axioms compensated_increment_norm_le_one
end SpectralRadiusUpperTail
