import SpectralRadiusUpperTail.RealSchurInvariantPlaneSpan
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The invariant span of a real eigenvector pair retains the prescribed
quadratic factor, not just its dimension. -/
theorem realInvariantPair_restriction
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) (u v : E) (a b : ℝ)
    (hLI : LinearIndependent ℝ ![u,v])
    (hu : f u = a • u - b • v) (hv : f v = b • u + a • v) :
    ∃ hInv : ∀ w ∈ Submodule.span ℝ (Set.range ![u,v]),
        f w ∈ Submodule.span ℝ (Set.range ![u,v]),
      LinearMap.toMatrix (Module.Basis.span hLI) (Module.Basis.span hLI) (f.restrict hInv) = !![a,b;-b,a] := by
  let P := Submodule.span ℝ (Set.range ![u,v])
  have huP : u ∈ P := Submodule.subset_span ⟨0,by simp⟩
  have hvP : v ∈ P := Submodule.subset_span ⟨1,by simp⟩
  have hInv : ∀ w ∈ P, f w ∈ P := by
    intro w hw
    refine Submodule.span_induction (fun x hx => ?_) ?_
      (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hw
    · obtain ⟨i,rfl⟩ := hx
      fin_cases i
      · simpa [hu] using
          P.sub_mem (P.smul_mem a huP) (P.smul_mem b hvP)
      · simpa [hv] using
          P.add_mem (P.smul_mem b huP) (P.smul_mem a hvP)
    · simpa using P.zero_mem
    · simpa only [map_add] using P.add_mem hx hy
    · simpa only [map_smul] using P.smul_mem c hx
  refine ⟨hInv,?_⟩
  have h0 : (f.restrict hInv) ((Module.Basis.span hLI) 0) =
      a • (Module.Basis.span hLI) 0 - b • (Module.Basis.span hLI) 1 := by
    apply Subtype.ext
    simpa using hu
  have h1 : (f.restrict hInv) ((Module.Basis.span hLI) 1) =
      b • (Module.Basis.span hLI) 0 + a • (Module.Basis.span hLI) 1 := by
    apply Subtype.ext
    simpa using hv
  ext i j
  fin_cases i <;> fin_cases j <;> rw [LinearMap.toMatrix_apply]
  · change ((Module.Basis.span hLI).repr
      ((f.restrict hInv) ((Module.Basis.span hLI) 0))) 0 = a
    rw [h0]
    simp only [map_sub,map_add,map_smul,Module.Basis.repr_self]
    norm_num
  · change ((Module.Basis.span hLI).repr
      ((f.restrict hInv) ((Module.Basis.span hLI) 1))) 0 = b
    rw [h1]
    simp only [map_sub,map_add,map_smul,Module.Basis.repr_self]
    norm_num
  · change ((Module.Basis.span hLI).repr
      ((f.restrict hInv) ((Module.Basis.span hLI) 0))) 1 = -b
    rw [h0]
    simp only [map_sub,map_add,map_smul,Module.Basis.repr_self]
    norm_num
  · change ((Module.Basis.span hLI).repr
      ((f.restrict hInv) ((Module.Basis.span hLI) 1))) 1 = a
    rw [h1]
    simp only [map_sub,map_add,map_smul,Module.Basis.repr_self]
    norm_num

theorem realInvariantPair_restrict_charpoly
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (u v : E) (a b : ℝ)
    (hLI : LinearIndependent ℝ ![u,v])
    (hu : f u = a • u - b • v) (hv : f v = b • u + a • v) :
    ∃ hInv : ∀ w ∈ Submodule.span ℝ (Set.range ![u,v]),
        f w ∈ Submodule.span ℝ (Set.range ![u,v]),
      (f.restrict hInv).charpoly =
        Polynomial.X^2 - Polynomial.C (2*a)*Polynomial.X + Polynomial.C (a^2+b^2) := by
  obtain ⟨hInv,hmat⟩ := realInvariantPair_restriction f u v a b hLI hu hv
  refine ⟨hInv,?_⟩
  have ht : (!![a,b;-b,a]).trace = 2*a := by simp [Matrix.trace_fin_two]; ring
  have hd : (!![a,b;-b,a]).det = a^2+b^2 := by simp [Matrix.det_fin_two]; ring
  rw [← (f.restrict hInv).charpoly_toMatrix (Module.Basis.span hLI),hmat,Matrix.charpoly_fin_two]
  rw [ht,hd]

#print axioms realInvariantPair_restriction
#print axioms realInvariantPair_restrict_charpoly
end SpectralRadiusUpperTail
