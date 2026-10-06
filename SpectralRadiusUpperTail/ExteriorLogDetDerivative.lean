import SpectralRadiusUpperTail.ShiftedDeterminantDerivative
import SpectralRadiusUpperTail.ComplexLogNormDerivative
import SpectralRadiusUpperTail.ExteriorLogDetNormalization
import SpectralRadiusUpperTail.NormalizedMatrixTrace
import Mathlib.Algebra.Algebra.Spectrum.Basic

namespace SpectralRadiusUpperTail

lemma trace_resolvent_det_ratio {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix.trace (resolvent A z) =
      Matrix.trace (Matrix.adjugate (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)) /
        Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A) := by
  change Matrix.trace (Ring.inverse (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z-A)) = _
  rw [Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_def, Matrix.trace_smul]
  simp [Ring.inverse_eq_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma shiftedDeterminant_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : z ∈ resolventSet ℂ A) :
    Matrix.det (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A) ≠ 0 := by
  have hh := (Matrix.isUnit_iff_isUnit_det _).mp (spectrum.mem_resolventSet_iff.mp hz)
  simpa only [Algebra.algebraMap_eq_smul_one, isUnit_iff_ne_zero] using hh

lemma normalizedExteriorLogDet_hasDerivAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℝ) (hb : (b : ℂ) ∈ resolventSet ℂ A) :
    HasDerivAt (normalizedExteriorLogDet A)
      (normalizedMatrixTrace (resolvent A (b : ℂ))).re b := by
  have hh := (complex_log_norm_hasDerivAt (shiftedDeterminant_hasDerivAt A (b : ℂ)).comp_ofReal
    (shiftedDeterminant_ne_zero A b hb)).div_const (n : ℝ)
  rw [← trace_resolvent_det_ratio] at hh
  convert! hh using 1
  change ((n : ℂ)⁻¹ * (resolvent A (b : ℂ)).trace).re = (resolvent A (b : ℂ)).trace.re/(n : ℝ)
  have he : (n : ℂ)⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

#print axioms trace_resolvent_det_ratio
#print axioms shiftedDeterminant_ne_zero
#print axioms normalizedExteriorLogDet_hasDerivAt
end SpectralRadiusUpperTail
