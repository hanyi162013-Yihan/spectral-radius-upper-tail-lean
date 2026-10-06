import SpectralRadiusUpperTail.RealSchurInvariantSubspaceSeed
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The one- or two-dimensional invariant seed is independent of the
chosen coordinates. This form can be applied recursively to an
orthogonal complement in a real-Schur construction. -/
theorem realLinearMap_exists_invariant_subspace_rank_one_or_two
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hE : 0 < Module.finrank ℝ E) (f : E →ₗ[ℝ] E) :
    ∃ P : Submodule ℝ E,
      (Module.finrank ℝ P = 1 ∨ Module.finrank ℝ P = 2) ∧
      ∀ x ∈ P, f x ∈ P := by
  let b := Module.finBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix b b f
  obtain ⟨P₀,hP₀,hInv⟩ := realMatrix_exists_invariant_subspace_rank_one_or_two hE A
  let P : Submodule ℝ E := P₀.map b.equivFun.symm.toLinearMap
  have hcoord (w : Fin (Module.finrank ℝ E) → ℝ) :
      f (b.equivFun.symm w) = b.equivFun.symm (A.mulVec w) := by
    apply b.equivFun.injective
    have h := LinearMap.toMatrix_mulVec_repr b b f (b.equivFun.symm w)
    change A.mulVec (b.equivFun (b.equivFun.symm w)) =
      b.equivFun (f (b.equivFun.symm w)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  refine ⟨P, ?_, ?_⟩
  · have hrank : Module.finrank ℝ P = Module.finrank ℝ P₀ :=
      b.equivFun.symm.finrank_map_eq P₀
    exact hrank ▸ hP₀
  · intro x hx
    obtain ⟨w,hw,rfl⟩ := Submodule.mem_map.mp hx
    change f (b.equivFun.symm w) ∈ P
    rw [hcoord]
    exact Submodule.mem_map_of_mem (hInv w hw)

#print axioms realLinearMap_exists_invariant_subspace_rank_one_or_two
end SpectralRadiusUpperTail
