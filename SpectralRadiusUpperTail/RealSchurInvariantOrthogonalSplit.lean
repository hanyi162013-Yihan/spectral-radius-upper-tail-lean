import SpectralRadiusUpperTail.RealSchurInvariantQuotient
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The orthogonal coordinates of an invariant subspace have a zero
lower-left block under the conjugated endomorphism. -/
theorem realLinearMap_invariant_orthogonal_lower_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P) (x : P) :
    (P.orthogonalDecomposition (f (x : E))).snd = 0 := by
  rw [P.snd_orthogonalDecomposition_apply]
  exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero
    (hP x x.property)

/-- Every nonzero finite-dimensional real inner-product endomorphism
has an orthogonal one- or two-dimensional leading block, whose
lower-left coupling is exactly zero. -/
theorem realLinearMap_exists_orthogonal_invariant_leading_block
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (hE : 0 < Module.finrank ℝ E) (f : E →ₗ[ℝ] E) :
    ∃ P : Submodule ℝ E,
      (Module.finrank ℝ P = 1 ∨ Module.finrank ℝ P = 2) ∧
      ∀ x : P, (P.orthogonalDecomposition (f (x : E))).snd = 0 := by
  obtain ⟨P,hRank,hInv⟩ :=
    realLinearMap_exists_invariant_subspace_rank_one_or_two hE f
  exact ⟨P,hRank,realLinearMap_invariant_orthogonal_lower_zero f P hInv⟩

#print axioms realLinearMap_exists_orthogonal_invariant_leading_block
end SpectralRadiusUpperTail
