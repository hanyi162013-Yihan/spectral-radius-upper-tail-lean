import SpectralRadiusUpperTail.RealSphereLogBound
import SpectralRadiusUpperTail.HalfGammaRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma real_sphere_rate_upper (u ell ε : ℝ) (hu : 0 < u) (hell : 0 < ell) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℝ, H.PosSemidef →
      Real.log (sphereQuadraticIntegral ℝ n ((n : ℝ)/(2*u)) H)/(n : ℝ) ≤
        (Real.log u+ell-1)/2-Real.log |(H+(ell*u) • (1 : Matrix (Fin n) (Fin n) ℝ)).det|/(2*(n : ℝ))+ε := by
  filter_upwards [half_gamma_rate_eventual_upper ε hε,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  intro H hH
  have hh := real_sphere_log_bound n (by omega) H hH ((n : ℝ)/(2*u)) (ell*u)
    (by positivity) (mul_pos hell hu)
  simp only [Real.norm_eq_abs] at hh
  have hlog : Real.log ((n : ℝ)/(2*u)) = Real.log ((n : ℝ)/2)-Real.log u := by
    rw [Real.log_div hnpos.ne' (by positivity),Real.log_mul (by norm_num) hu.ne',
      Real.log_div hnpos.ne' (by norm_num)]
    ring
  rw [hlog] at hh
  have hd := div_le_div_of_nonneg_right hh hnpos.le
  have he : (((n : ℝ)/(2*u))*(ell*u)+Real.log (Real.Gamma ((n : ℝ)/2+1))-
      ((n : ℝ)*(Real.log ((n : ℝ)/2)-Real.log u)+
        Real.log |(H+(ell*u) • (1 : Matrix (Fin n) (Fin n) ℝ)).det|)/2)/(n : ℝ) =
      ell/2+Real.log u/2+(Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ)-Real.log ((n : ℝ)/2)/2)-
        Real.log |(H+(ell*u) • (1 : Matrix (Fin n) (Fin n) ℝ)).det|/(2*(n : ℝ)) := by
    field_simp
    <;> ring
  rw [he] at hd
  linarith

#print axioms real_sphere_rate_upper
end SpectralRadiusUpperTail
