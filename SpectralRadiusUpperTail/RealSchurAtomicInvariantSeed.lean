import SpectralRadiusUpperTail.RealSchurInvariantSubspaceGeneral
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

namespace SpectralRadiusUpperTail

/-- A real eigenvalue supplies an invariant line in arbitrary coordinates. -/
theorem realLinearMap_realEigenvalue_invariant_line
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (a : ℝ) (ha : Module.End.HasEigenvalue f a) :
    ∃ P : Submodule ℝ E, Module.finrank ℝ P=1 ∧ ∀ x ∈ P, f x ∈ P := by
  obtain ⟨u,hu⟩ := ha.exists_hasEigenvector
  let P : Submodule ℝ E := Submodule.span ℝ {u}
  have hdim : Module.finrank ℝ P=1 := by
    simpa only [P] using finrank_span_singleton hu.2
  refine ⟨P,hdim,?_⟩
  intro x hx
  refine Submodule.span_induction (fun v hv => ?_) ?_
    (fun v w _ _ hv hw => ?_) (fun b v _ hv => ?_) hx
  · have hvu : v=u := by simpa using hv
    rw [hvu,hu.apply_eq_smul]
    exact P.smul_mem a (Submodule.subset_span (by simp))
  · simp
  · rw [map_add]
    exact P.add_mem hv hw
  · rw [map_smul]
    exact P.smul_mem b hv

/-- An invariant restriction of an operator without real eigenvalues
also has no real characteristic root. -/
theorem realLinearMap_noRealRoot_restrict
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (hno : ∀ a : ℝ, ¬ Module.End.HasEigenvalue f a)
    (P : Submodule ℝ E) (hP : ∀ x ∈ P, f x ∈ P) :
    ∀ a : ℝ, (f.restrict hP).charpoly.eval a ≠ 0 := by
  intro a ha
  have hroot : (f.restrict hP).charpoly.IsRoot a := ha
  obtain ⟨v,hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ a).mpr hroot).exists_hasEigenvector
  have hEq : f (v : E)=a • (v : E) := congrArg Subtype.val hv.apply_eq_smul
  have hne : (v : E) ≠ 0 := by
    intro hz
    apply hv.2
    exact Subtype.ext hz
  apply hno a
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hEq,hne⟩

/-- Choose a real eigenline whenever possible. Otherwise any invariant
one/two-dimensional seed has no real roots on its restriction. Thus every
two-dimensional seed is an indivisible conjugate pair. -/
theorem realLinearMap_exists_atomic_invariant_seed
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hE : 0 < Module.finrank ℝ E) (f : E →ₗ[ℝ] E) :
    ∃ P : Submodule ℝ E,
      (Module.finrank ℝ P=1 ∨ Module.finrank ℝ P=2) ∧
      ∃ hP : ∀ x ∈ P, f x ∈ P,
        Module.finrank ℝ P=2 → ∀ a : ℝ, (f.restrict hP).charpoly.eval a ≠ 0 := by
  classical
  by_cases hr : ∃ a : ℝ, Module.End.HasEigenvalue f a
  · obtain ⟨a,ha⟩ := hr
    obtain ⟨P,hP,hInv⟩ := realLinearMap_realEigenvalue_invariant_line f a ha
    exact ⟨P,Or.inl hP,hInv,fun htwo => by omega⟩
  · obtain ⟨P,hP,hInv⟩ := realLinearMap_exists_invariant_subspace_rank_one_or_two hE f
    refine ⟨P,hP,hInv,fun _ => ?_⟩
    exact realLinearMap_noRealRoot_restrict f (fun a ha => hr ⟨a,ha⟩) P hInv

#print axioms realLinearMap_realEigenvalue_invariant_line
#print axioms realLinearMap_noRealRoot_restrict
#print axioms realLinearMap_exists_atomic_invariant_seed
end SpectralRadiusUpperTail
