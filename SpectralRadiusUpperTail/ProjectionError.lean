import SpectralRadiusUpperTail.HilbertCovariance
import Mathlib.Analysis.Complex.Basic

namespace SpectralRadiusUpperTail

lemma linear_score_error_combine (p D g c R S : ℝ)
    (hR : |p+c*D| ≤ R) (hS : |D+g| ≤ S) :
    |p-c*g| ≤ R+|c| *S := by
  have he : p-c*g = (p+c*D)-c*(D+g) := by ring
  rw [he]
  calc
    _ ≤ |p+c*D|+|c*(D+g)| := abs_sub _ _
    _ = |p+c*D|+|c| * |D+g| := by rw [abs_mul]
    _ ≤ _ := add_le_add hR (mul_le_mul_of_nonneg_left hS (abs_nonneg c))

lemma norm_le_of_projection_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (C : ℝ) (hC : 0 ≤ C) (h : ∀ w : E, |inner ℝ w z| ≤ C*‖w‖) :
    ‖z‖ ≤ C := by
  have hh := h z
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
  by_cases hz : ‖z‖ = 0
  · simpa only [hz] using hC
  · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    nlinarith

lemma complex_projection_conj_mul (w b s : ℂ) :
    inner ℝ w (star b*s) = inner ℝ s (b*w) := by
  simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply', RCLike.re_eq_complex_re,
    Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma complex_projection_scaled_regression (w b s : ℂ) (d : ℝ) :
    inner ℝ w ((1/d : ℝ) • (star b*s)) = inner ℝ s (b*w)/d := by
  rw [real_inner_smul_right, complex_projection_conj_mul]
  ring

#print axioms norm_le_of_projection_error
#print axioms complex_projection_scaled_regression
end SpectralRadiusUpperTail
