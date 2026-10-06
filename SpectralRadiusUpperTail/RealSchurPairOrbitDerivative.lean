import SpectralRadiusUpperTail.RealSchurPairRotation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

private theorem sin_mul_cos_hasDerivAt_zero :
    HasDerivAt (fun θ : ℝ => Real.sin θ * Real.cos θ) 1 0 := by
  have h := (Real.hasDerivAt_sin (0 : ℝ)).mul
    (Real.hasDerivAt_cos (0 : ℝ))
  convert h using 1 <;> try rfl
  all_goals simp

private theorem cos_sq_hasDerivAt_zero :
    HasDerivAt (fun θ : ℝ => (Real.cos θ)^2) 0 0 := by
  have h := (Real.hasDerivAt_cos (0 : ℝ)).pow 2
  convert h using 1 <;> try rfl
  all_goals simp

private theorem sin_sq_hasDerivAt_zero :
    HasDerivAt (fun θ : ℝ => (Real.sin θ)^2) 0 0 := by
  have h := (Real.hasDerivAt_sin (0 : ℝ)).pow 2
  convert h using 1 <;> try rfl
  all_goals simp

private theorem orbit_diag_first_hasDerivAt_zero (x b c : ℝ) :
    HasDerivAt (fun θ : ℝ =>
      x+(c-b)*(Real.sin θ*Real.cos θ)) (c-b) 0 := by
  have h := (sin_mul_cos_hasDerivAt_zero.const_mul (c-b)).const_add x
  convert h using 1 <;> try rfl
  all_goals simp

private theorem orbit_diag_last_hasDerivAt_zero (x b c : ℝ) :
    HasDerivAt (fun θ : ℝ =>
      x+(b-c)*(Real.sin θ*Real.cos θ)) (b-c) 0 := by
  have h := (sin_mul_cos_hasDerivAt_zero.const_mul (b-c)).const_add x
  convert h using 1 <;> try rfl
  all_goals simp

private theorem orbit_upper_hasDerivAt_zero (b c : ℝ) :
    HasDerivAt (fun θ : ℝ =>
      b*(Real.cos θ)^2+c*(Real.sin θ)^2) 0 0 := by
  have h := (cos_sq_hasDerivAt_zero.const_mul b).add
    (sin_sq_hasDerivAt_zero.const_mul c)
  convert h using 1 <;> try rfl
  all_goals simp

private theorem orbit_lower_hasDerivAt_zero (b c : ℝ) :
    HasDerivAt (fun θ : ℝ =>
      -(c*(Real.cos θ)^2+b*(Real.sin θ)^2)) 0 0 := by
  have h := ((cos_sq_hasDerivAt_zero.const_mul c).add
    (sin_sq_hasDerivAt_zero.const_mul b)).neg
  convert h using 1 <;> try rfl
  all_goals simp

/-- Every matrix entry of the actual orthogonal-conjugation orbit has
derivative equal to the commutator column used in the 4×4 Jacobian. -/
theorem realSchur_rotation_orbit_hasDerivAt_zero
    (x b c : ℝ) (i j : Fin 2) :
    HasDerivAt (fun θ : ℝ =>
      (realSchurRotation θ * realSchurBlock x b c *
        (realSchurRotation θ)ᵀ) i j)
      ((realSchurRotationGenerator * realSchurBlock x b c -
        realSchurBlock x b c * realSchurRotationGenerator) i j) 0 := by
  have heq : (fun θ : ℝ =>
      (realSchurRotation θ * realSchurBlock x b c *
        (realSchurRotation θ)ᵀ) i j) =
      (fun θ : ℝ => realSchurRotatedBlock θ x b c i j) := by
    funext θ
    rw [realSchurRotation_conjugate_block]
  rw [heq, realSchur_pair_orbit_commutator]
  fin_cases i <;> fin_cases j
  · simpa [realSchurRotatedBlock, mul_assoc] using
      orbit_diag_first_hasDerivAt_zero x b c
  · simpa [realSchurRotatedBlock] using
      orbit_upper_hasDerivAt_zero b c
  · simpa [realSchurRotatedBlock] using
      orbit_lower_hasDerivAt_zero b c
  · simpa [realSchurRotatedBlock, mul_assoc] using
      orbit_diag_last_hasDerivAt_zero x b c

#print axioms sin_mul_cos_hasDerivAt_zero
#print axioms cos_sq_hasDerivAt_zero
#print axioms sin_sq_hasDerivAt_zero
#print axioms orbit_diag_first_hasDerivAt_zero
#print axioms orbit_diag_last_hasDerivAt_zero
#print axioms orbit_upper_hasDerivAt_zero
#print axioms orbit_lower_hasDerivAt_zero
#print axioms realSchur_rotation_orbit_hasDerivAt_zero
end SpectralRadiusUpperTail
