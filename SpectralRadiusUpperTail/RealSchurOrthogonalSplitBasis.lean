import SpectralRadiusUpperTail.RealSchurInvariantOrthogonalSplit
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- An orthonormal basis adapted to a subspace and its orthogonal
complement, indexed by the two component dimensions. -/
noncomputable def realSchurOrthogonalSplitBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ E) :
    OrthonormalBasis
      ((Fin (Module.finrank ℝ P)) ⊕ (Fin (Module.finrank ℝ Pᗮ))) ℝ E :=
  ((stdOrthonormalBasis ℝ P).prod (stdOrthonormalBasis ℝ Pᗮ)).map
    P.orthogonalDecomposition.symm

theorem realSchurOrthogonalSplitBasis_inl_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ E)
    (i : Fin (Module.finrank ℝ P)) :
    realSchurOrthogonalSplitBasis P (Sum.inl i) ∈ P := by
  simp [realSchurOrthogonalSplitBasis, OrthonormalBasis.prod_apply,
    OrthonormalBasis.map_apply]

theorem realSchurOrthogonalSplitBasis_inr_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (P : Submodule ℝ E)
    (i : Fin (Module.finrank ℝ Pᗮ)) :
    realSchurOrthogonalSplitBasis P (Sum.inr i) ∈ Pᗮ := by
  simp [realSchurOrthogonalSplitBasis, OrthonormalBasis.prod_apply,
    OrthonormalBasis.map_apply]

#print axioms realSchurOrthogonalSplitBasis_inl_mem
#print axioms realSchurOrthogonalSplitBasis_inr_mem
end SpectralRadiusUpperTail
