import SpectralRadiusUpperTail.ComplexSphereLogBound
import SpectralRadiusUpperTail.LogFactorialRate

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

lemma complex_sphere_rate_upper (u ell ε : ℝ) (hu : 0 < u) (hell : 0 < ell) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef →
      Real.log (sphereQuadraticIntegral ℂ n ((n : ℝ)/u) H)/(n : ℝ) ≤
        Real.log u+ell-1-Real.log ‖(H+((ell*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖/(n : ℝ)+ε := by
  have ht := (tendsto_order.1 log_factorial_rate_limit).2 (-1+ε) (by linarith)
  filter_upwards [ht,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  intro H hH
  have hh := complex_sphere_log_bound n (by omega) H hH ((n : ℝ)/u) (ell*u)
    (div_pos hnpos hu) (mul_pos hell hu)
  rw [Real.log_div hnpos.ne' hu.ne'] at hh
  have hd := div_le_div_of_nonneg_right hh hnpos.le
  have he : (((n : ℝ)/u)*(ell*u)+Real.log (n.factorial : ℝ)-
      (n : ℝ)*(Real.log (n : ℝ)-Real.log u)-
      Real.log ‖(H+((ell*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖)/(n : ℝ) =
      ell+Real.log u+(Real.log (n.factorial : ℝ)/(n : ℝ)-Real.log (n : ℝ))-
      Real.log ‖(H+((ell*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖/(n : ℝ) := by
    field_simp
    <;> ring
  rw [he] at hd
  linarith

#print axioms complex_sphere_rate_upper
end SpectralRadiusUpperTail
