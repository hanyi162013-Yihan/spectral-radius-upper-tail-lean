import SpectralRadiusUpperTail.ComplexSphereWitness

namespace SpectralRadiusUpperTail
open scoped ENNReal ComplexOrder MatrixOrder

lemma complex_sphere_witness_log (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) (d : ℝ)
    (hd : (inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ) H v)).re ≤ d) :
    (n : ℝ)*(Real.log u-1-d/u)-
      Real.log ‖(H+((2*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ ≤
        Real.log (sphereQuadraticIntegral ℂ n ((n : ℝ)/u) H) := by
  have hdet : 0 < ‖(H+((2*u : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖ := by
    have hh := (posSemidef_shift_det_lower H hH (2*u) (by positivity)).1
    have hp : 0 < (2*u)^n := pow_pos (by positivity) n
    exact hp.trans_le (by convert! hh using 1)
  have hZ := sphereQuadraticIntegral_pos ℂ n hn ((n : ℝ)/u) (by positivity) H hH
  have hh := complex_sphere_witness n hn u hu H hH v hv d hd
  have hr := (ENNReal.ofReal_le_ofReal_iff hZ.le).mp hh
  have hl := Real.log_le_log (by positivity) hr
  rw [Real.log_div (by positivity) hdet.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow] at hl
  convert! hl using 1
  ring

#print axioms complex_sphere_witness_log
end SpectralRadiusUpperTail
