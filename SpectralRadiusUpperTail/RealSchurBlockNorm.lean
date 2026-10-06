import SpectralRadiusUpperTail.RealSchurBlockPower
import SpectralRadiusUpperTail.SchurPowerBuffer
import SpectralRadiusUpperTail.SpectralWitness

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

/-- Exact squared Frobenius power identity for a real Schur block. The
nonnormality enters only through the squared gap (b-c)^2. -/
lemma real_schur_block_hs_identity (x b c y : ℝ) (hy : y ≠ 0)
    (hbc : b*c = y^2) (k : ℕ) :
    ‖(realSchurBlock x b c)^k‖^2 =
      2*‖(x : ℂ)+y*Complex.I‖^(2*k)+
        ((b-c)/y)^2*((((x : ℂ)+y*Complex.I)^k).im)^2 := by
  have hz : ‖(x : ℂ)+y*Complex.I‖^(2*k) =
      ((((x : ℂ)+y*Complex.I)^k).re)^2+((((x : ℂ)+y*Complex.I)^k).im)^2 := by
    rw [Nat.mul_comm 2 k, pow_mul, ← norm_pow, Complex.sq_norm]
    simp [Complex.normSq, pow_two]
  rw [real_frobenius_norm_sq, real_schur_block_power_formula x b c y hy hbc k, hz]
  simp [Fin.sum_univ_two]
  field_simp [hy]
  nlinarith [congrArg (fun t : ℝ => t*((((x : ℂ)+y*Complex.I)^k).im)^2) hbc]

lemma real_schur_block_hs_derivative_bound (x b c y : ℝ) (hy : 0 < y)
    (hbc : b*c = y^2) (k : ℕ) :
    ‖(realSchurBlock x b c)^(k+1)‖^2 ≤
      2*‖(x : ℂ)+y*Complex.I‖^(2*(k+1))+
        (b-c)^2*(((k+1 : ℕ) : ℝ)*‖(x : ℂ)+y*Complex.I‖^k)^2 := by
  have hi := complex_power_im_le ((x : ℂ)+y*Complex.I) k
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
    abs_of_pos hy] at hi
  have hs := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs] at hs
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg ((b-c)/y))
  have he : ((b-c)/y)^2*(((k+1 : ℕ) : ℝ)*‖(x : ℂ)+y*Complex.I‖^k*y)^2 =
      (b-c)^2*(((k+1 : ℕ) : ℝ)*‖(x : ℂ)+y*Complex.I‖^k)^2 := by
    field_simp
  rw [he] at hh
  rw [real_schur_block_hs_identity x b c y hy.ne' hbc]
  exact add_le_add le_rfl hh

/-- Uniform deterministic block bound, including the zeroth power. -/
theorem real_schur_block_hs_buffer (x b c y ε : ℝ) (hy : 0 < y) (hε : 0 < ε)
    (hbc : b*c = y^2) (k : ℕ) :
    ‖(realSchurBlock x b c)^k‖^2 ≤
      (2+(b-c)^2/ε^2)*(‖(x : ℂ)+y*Complex.I‖+ε)^(2*k) := by
  cases k with
  | zero =>
    rw [real_schur_block_hs_identity x b c y hy.ne' hbc]
    simp
    positivity
  | succ k =>
    exact (real_schur_block_hs_derivative_bound x b c y hy hbc k).trans
      (schur_squared_power_buffer _ ε (b-c) (norm_nonneg _) hε k)

#print axioms real_schur_block_hs_identity
#print axioms real_schur_block_hs_buffer
end SpectralRadiusUpperTail
