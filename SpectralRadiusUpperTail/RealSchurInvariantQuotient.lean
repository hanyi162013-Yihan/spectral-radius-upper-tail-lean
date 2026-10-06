import SpectralRadiusUpperTail.RealSchurInvariantSubspaceGeneral
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- An invariant subspace induces an endomorphism on its quotient. -/
def realLinearMapInvariantQuotient
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P) : E ⧸ P →ₗ[ℝ] E ⧸ P :=
  P.mapQ P f (by intro x hx; exact hP x hx)

@[simp] theorem realLinearMapInvariantQuotient_mkQ
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P) (x : E) :
    realLinearMapInvariantQuotient f P hP (P.mkQ x) = P.mkQ (f x) :=
  Submodule.mapQ_apply P P f x

/-- Pulling an invariant quotient subspace back gives an invariant
subspace of the original endomorphism. -/
theorem realLinearMapInvariantQuotient_comap_invariant
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P)
    (Q : Submodule ℝ (E ⧸ P))
    (hQ : ∀ y ∈ Q, realLinearMapInvariantQuotient f P hP y ∈ Q) :
    ∀ x ∈ Q.comap P.mkQ, f x ∈ Q.comap P.mkQ := by
  intro x hx
  change P.mkQ (f x) ∈ Q
  rw [← realLinearMapInvariantQuotient_mkQ f P hP x]
  exact hQ (P.mkQ x) hx

/-- The quotient dimension drops by at least one at every real-Schur
seed step, so induction on finite dimension can use this quotient. -/
theorem realLinearMap_exists_invariant_quotient_step
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (hE : 0 < Module.finrank ℝ E) (f : E →ₗ[ℝ] E) :
    ∃ P : Submodule ℝ E,
      (Module.finrank ℝ P = 1 ∨ Module.finrank ℝ P = 2) ∧
      (∀ x ∈ P, f x ∈ P) ∧
      Module.finrank ℝ (E ⧸ P) < Module.finrank ℝ E := by
  obtain ⟨P,hRank,hInv⟩ :=
    realLinearMap_exists_invariant_subspace_rank_one_or_two hE f
  refine ⟨P,hRank,hInv,?_⟩
  have hsum := P.finrank_quotient_add_finrank
  rcases hRank with hRank | hRank <;> omega

#print axioms realLinearMapInvariantQuotient_comap_invariant
#print axioms realLinearMap_exists_invariant_quotient_step
end SpectralRadiusUpperTail
