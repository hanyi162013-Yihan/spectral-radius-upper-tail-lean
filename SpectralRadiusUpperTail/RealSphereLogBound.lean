import SpectralRadiusUpperTail.RealRegularizedSphere
import SpectralRadiusUpperTail.SphereQuadraticIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma real_sphere_log_bound (n : ℕ) (hn : 0 < n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    Real.log (sphereQuadraticIntegral ℝ n c H) ≤ c*s+Real.log (Real.Gamma ((n : ℝ)/2+1))-
      ((n : ℝ)*Real.log c+Real.log ‖(H+(s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det‖)/2 := by
  have hd : 0 < ‖(H+(s : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det‖ :=
    norm_pos_iff.mpr (ne_of_gt (matrix_regularized_posDef H hH s hs).det_pos)
  have hh := real_regularized_sphere_bound n hn H hH c s hc hs
  have he := sphereQuadraticIntegral_lintegral ℝ n hn c hc.le H hH
  simp only [RCLike.re_to_real] at he
  rw [← he] at hh
  simp only [Real.norm_eq_abs] at hd ⊢
  have hG := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2+1)
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hl := Real.log_le_log (sphereQuadraticIntegral_pos ℝ n hn c hc.le H hH) hr
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_exp,Real.log_sqrt (by positivity),Real.log_mul (by positivity) hd.ne',Real.log_pow] at hl
  linarith

#print axioms real_sphere_log_bound
end SpectralRadiusUpperTail
