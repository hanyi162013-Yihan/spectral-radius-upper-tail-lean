import SpectralRadiusUpperTail.SpectralUnitEigenvector
import SpectralRadiusUpperTail.ShiftedDeterminantRoots
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

namespace SpectralRadiusUpperTail
open scoped Matrix.Norms.L2Operator

lemma matrix_radius_eigenvalue {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ z ∈ spectrum ℂ A, ‖z‖ = (spectralRadius ℂ A).toReal := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : (spectrum ℂ A).Nonempty := by
    obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue A.toLin'
    exact ⟨z, by simpa using hz.mem_spectrum⟩
  obtain ⟨z, hz, he⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hs
  refine ⟨z, hz, ?_⟩
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.coe_toReal, coe_nnnorm] using hh

lemma matrix_radius_annulus_eigenvalue {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (r R : ℝ)
    (hr : r ≤ (spectralRadius ℂ A).toReal)
    (hR : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ ≤ R) :
    ∃ z ∈ spectrum ℂ A, r ≤ ‖z‖ ∧ ‖z‖ ≤ R := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨z, hz, he⟩ := matrix_radius_eigenvalue hn A
  refine ⟨z, hz, by rwa [he], ?_⟩
  exact (spectrum.norm_le_norm_of_mem hz).trans hR

#print axioms matrix_radius_eigenvalue
#print axioms matrix_radius_annulus_eigenvalue
end SpectralRadiusUpperTail
