import SpectralRadiusUpperTail.SquareExpMixedMomentBound
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma factorial_moment_envelope_le (M u : ℝ) (hM : 0 ≤ M) (hu : 0 ≤ u)
    (d N : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    (1+(d.factorial : ℝ)*u^d)*M ≤
      (max 1 (2*M)*(((N : ℝ)+1)*(1+u)))^d := by
  let T : ℝ := ((N : ℝ)+1)*(1+u)
  let A : ℝ := max 1 (2*M)
  have hT : 1 ≤ T := by
    dsimp [T]
    nlinarith [(show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  have hA : 1 ≤ A := le_max_left _ _
  have hM2 : 2*M ≤ A := le_max_right _ _
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdN' : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
  have hdu : (d : ℝ)*u ≤ T := by
    dsimp [T]
    nlinarith [mul_le_mul_of_nonneg_right hdN' hu, (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  have hf : (d.factorial : ℝ) ≤ (d : ℝ)^d := by exact_mod_cast Nat.factorial_le_pow d
  have hfac : (d.factorial : ℝ)*u^d ≤ T^d := by
    calc
      _ ≤ (d : ℝ)^d*u^d := mul_le_mul_of_nonneg_right hf (pow_nonneg hu _)
      _ = ((d : ℝ)*u)^d := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hd0 hu) hdu d
  have hTd : 1 ≤ T^d := one_le_pow₀ hT
  have hAd : A ≤ A^d := by
    simpa only [pow_one] using pow_le_pow_right₀ hA hd
  change (1+(d.factorial : ℝ)*u^d)*M ≤ (A*T)^d
  rw [mul_pow]
  have hmul := mul_le_mul_of_nonneg_right (hM2.trans hAd) (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hTd)
  nlinarith

#print axioms factorial_moment_envelope_le
end SpectralRadiusUpperTail
