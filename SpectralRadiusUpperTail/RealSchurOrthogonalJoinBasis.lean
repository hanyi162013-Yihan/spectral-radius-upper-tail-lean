import SpectralRadiusUpperTail.RealSchurOrthogonalSplitMatrix
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Join orthonormal bases of a subspace and its orthogonal
complement into an orthonormal basis of the full space. -/
noncomputable def realSchurOrthogonalJoinBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : OrthonormalBasis ι ℝ P)
    (v : OrthonormalBasis κ ℝ Pᗮ) :
    OrthonormalBasis (ι ⊕ κ) ℝ E :=
  (u.prod v).map P.orthogonalDecomposition.symm

@[simp] theorem realSchurOrthogonalJoinBasis_inl
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : OrthonormalBasis ι ℝ P)
    (v : OrthonormalBasis κ ℝ Pᗮ) (i : ι) :
    realSchurOrthogonalJoinBasis P u v (Sum.inl i) = (u i : E) := by
  simp [realSchurOrthogonalJoinBasis, OrthonormalBasis.prod_apply,
    OrthonormalBasis.map_apply]

@[simp] theorem realSchurOrthogonalJoinBasis_inr
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : OrthonormalBasis ι ℝ P)
    (v : OrthonormalBasis κ ℝ Pᗮ) (i : κ) :
    realSchurOrthogonalJoinBasis P u v (Sum.inr i) = (v i : E) := by
  simp [realSchurOrthogonalJoinBasis, OrthonormalBasis.prod_apply,
    OrthonormalBasis.map_apply]

#print axioms realSchurOrthogonalJoinBasis_inl
#print axioms realSchurOrthogonalJoinBasis_inr
end SpectralRadiusUpperTail
