import SpectralRadiusUpperTail.ComplexRegularizedSphere
import SpectralRadiusUpperTail.SphereQuadraticIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma complex_sphere_log_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    Real.log (sphereQuadraticIntegral ℂ n c H) ≤ c*s+Real.log (n.factorial : ℝ)-
      (n : ℝ)*Real.log c-Real.log ‖(H+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ := by
  have hd : 0 < ‖(H+(s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ :=
    norm_pos_iff.mpr (ne_of_gt (matrix_regularized_posDef H hH s hs).det_pos)
  have hh := complex_regularized_sphere_bound n hn H hH c s hc hs
  have he := sphereQuadraticIntegral_lintegral ℂ n hn c hc.le H hH
  simp only [RCLike.re_eq_complex_re] at he
  rw [← he] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hl := Real.log_le_log (sphereQuadraticIntegral_pos ℂ n hn c hc.le H hH) hr
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_exp,Real.log_mul (by positivity) hd.ne',Real.log_pow] at hl
  linarith

#print axioms complex_sphere_log_bound
end SpectralRadiusUpperTail
