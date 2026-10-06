import SpectralRadiusUpperTail.MarkedRealEigenlineMultiplicity
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Every real characteristic root has a unit eigenvector; in a
simple-spectrum matrix its only unit marks are this vector and its
negative. -/
theorem exists_unit_real_eigenvector_of_charpoly_root
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (x : ℝ)
    (hx : f.charpoly.IsRoot x) :
    ∃ v : E, ‖v‖ = 1 ∧ f v = x • v := by
  have heig : Module.End.HasEigenvalue f x :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f x).mpr hx
  obtain ⟨w,hw⟩ := heig.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  refine ⟨(‖w‖)⁻¹ • w, ?_, ?_⟩
  · simp [norm_smul, Real.norm_eq_abs, abs_of_pos hnorm,
      hnorm.ne']
  · rw [map_smul, hw.apply_eq_smul]
    simp only [smul_smul]
    congr 1
    ring

#print axioms exists_unit_real_eigenvector_of_charpoly_root
end SpectralRadiusUpperTail
