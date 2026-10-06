import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma matrix_exists_unit_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : z ∈ spectrum ℂ A) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧ Matrix.toEuclideanCLM (𝕜 := ℂ) A v = z • v := by
  have he : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) z :=
    Module.End.HasEigenvalue.of_mem_spectrum (by rwa [Matrix.spectrum_toEuclideanLin])
  obtain ⟨w, hw⟩ := he.exists_hasEigenvector
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw.2
  have hwe : Matrix.toEuclideanCLM (𝕜 := ℂ) A w = z • w := by
    convert! hw.apply_eq_smul using 1
  refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), inv_mul_cancel₀ hw0]
  · rw [map_smul, hwe, smul_comm]

lemma matrix_eigenvector_residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (ζ z : ℂ) (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1)
    (he : Matrix.toEuclideanCLM (𝕜 := ℂ) A v = ζ • v) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A-z • 1) v‖^2 = ‖ζ-z‖^2 := by
  have hh : Matrix.toEuclideanCLM (𝕜 := ℂ) (A-z • 1) v = (ζ-z) • v := by
    simp only [map_sub, map_smul, map_one, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, he, sub_smul]
  rw [hh, norm_smul, hv, mul_one]

#print axioms matrix_exists_unit_eigenvector
#print axioms matrix_eigenvector_residual
end SpectralRadiusUpperTail
