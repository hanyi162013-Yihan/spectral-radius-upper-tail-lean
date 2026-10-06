import SpectralRadiusUpperTail.TraceGoodEvent

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

lemma phase_resolvent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q z : ℂ) (hq : q ≠ 0) : resolvent (q⁻¹ • A) z = q • resolvent A (q*z) := by
  have he := spectrum.units_smul_resolvent (r := Units.mk0 q hq) (a := A) (s := q*z)
  simpa only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val, smul_eq_mul,
    inv_mul_cancel_left₀ hq] using he.symm

lemma phase_resolventSet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q z : ℂ) (hq : q ≠ 0) (hz : q*z ∈ resolventSet ℂ A) :
    z ∈ resolventSet ℂ (q⁻¹ • A) := by
  rw [spectrum.isUnit_resolvent, phase_resolvent A q z hq]
  simpa only [Units.smul_def, Units.val_mk0] using
    IsUnit.smul (Units.mk0 q hq) (spectrum.isUnit_resolvent.mp hz)

lemma matrixTraceControl_phase {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (q : ℂ) (hq : ‖q‖ = 1) (r ε : ℝ) (h : matrixTraceControl A r ε) :
    matrixTraceControl (q⁻¹ • A) r ε := by
  have hq0 : q ≠ 0 := by intro he; simp [he] at hq
  intro z hz
  have hqz : r ≤ ‖q*z‖ := by simpa only [norm_mul, hq, one_mul] using hz
  refine ⟨phase_resolventSet A q z hq0 (h (q*z) hqz).1, ?_⟩
  rw [phase_resolvent A q z hq0, normalizedMatrixTrace_smul]
  have he : q*normalizedMatrixTrace (resolvent A (q*z))-z⁻¹ =
      q*(normalizedMatrixTrace (resolvent A (q*z))-(q*z)⁻¹) := by
    rw [mul_sub, mul_inv_rev]
    have hi : q*(z⁻¹*q⁻¹) = z⁻¹ := by
      rw [mul_left_comm, mul_inv_cancel₀ hq0, mul_one]
    rw [hi]
  rw [he, norm_mul, hq, one_mul]
  exact (h (q*z) hqz).2

#print axioms phase_resolvent
#print axioms phase_resolventSet
#print axioms matrixTraceControl_phase
end SpectralRadiusUpperTail
