import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
variable {n : ℕ}

/-- The Frobenius bound is proved from an actual nonzero eigenvector. -/
theorem complex_eigenvalue_le_frobenius {A : Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (hz : z ∈ spectrum ℂ A) : ‖z‖ ≤ ‖A‖ := by
  have he : Module.End.HasEigenvalue A.toLin' z :=
    Module.End.HasEigenvalue.of_mem_spectrum (by simpa using hz)
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  let B : Matrix (Fin n) (Fin 1) ℂ := Matrix.replicateCol (Fin 1) v
  have hB : B ≠ 0 := by
    intro h
    apply hv.2
    funext i
    exact congrFun (congrFun h i) 0
  have hmul : A * B = z • B := by
    ext i j
    have hi := congrFun hv.apply_eq_smul i
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, Matrix.mul_apply, Matrix.smul_apply, Matrix.replicateCol_apply, B] using hi
  have hbpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h := Matrix.frobenius_norm_mul A B
  rw [hmul, norm_smul] at h
  exact (mul_le_mul_iff_left₀ hbpos).mp h

/-- No norm-one assumption is needed for the Frobenius matrix norm. -/
theorem complex_spectralRadius_le_frobenius (A : Matrix (Fin n) (Fin n) ℂ) :
    spectralRadius ℂ A ≤ (‖A‖₊ : ℝ≥0∞) := by
  apply iSup₂_le
  intro z hz
  exact_mod_cast complex_eigenvalue_le_frobenius hz

theorem complex_spectralRadius_power_le_frobenius
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (hk : k ≠ 0) :
    (spectralRadius ℂ A).toReal ^ k ≤ ‖A^k‖ := by
  have h := (spectrum.spectralRadius_pow_le A k hk).trans
    (complex_spectralRadius_le_frobenius (A^k))
  have ht := ENNReal.toReal_mono (by simp) h
  simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm] using ht

lemma real_frobenius_norm_sq (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _))

lemma complexified_frobenius_power_norm (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    ‖(A.map Complex.ofRealHom)^k‖ = ‖A^k‖ := by
  rw [← Matrix.map_pow]
  exact Matrix.frobenius_norm_map_eq _ _ (fun a => Complex.norm_real a)

noncomputable def realMatrixRadius (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (spectralRadius ℂ (A.map Complex.ofRealHom)).toReal

/-- The deterministic power witness for the ordinary complex spectral radius of a real matrix. -/
theorem realMatrixRadius_power_sq_le (A : Matrix (Fin n) (Fin n) ℝ)
    (k : ℕ) (hk : k ≠ 0) :
    (realMatrixRadius A ^ k)^2 ≤ ∑ i, ∑ j, ((A^k) i j)^2 := by
  have h := complex_spectralRadius_power_le_frobenius (A.map Complex.ofRealHom) k hk
  rw [complexified_frobenius_power_norm] at h
  have hp : 0 ≤ realMatrixRadius A ^ k := pow_nonneg ENNReal.toReal_nonneg _
  have hs := mul_self_le_mul_self hp h
  simpa only [← sq, realMatrixRadius, real_frobenius_norm_sq] using hs

#print axioms complex_eigenvalue_le_frobenius
#print axioms complex_spectralRadius_power_le_frobenius
#print axioms realMatrixRadius_power_sq_le
end SpectralRadiusUpperTail
