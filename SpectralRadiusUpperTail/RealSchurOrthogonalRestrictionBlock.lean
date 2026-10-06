import SpectralRadiusUpperTail.RealSchurOrthogonalCompression

namespace SpectralRadiusUpperTail
open scoped InnerProductSpace

/-- The leading block in a joined orthonormal basis is the invariant
restriction, written in the chosen basis of the invariant subspace. -/
theorem realSchurOrthogonalJoinBasis_upperLeft_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E) (hP : ∀ x ∈ P, f x ∈ P)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (u : OrthonormalBasis ι ℝ P) (v : OrthonormalBasis κ ℝ Pᗮ) (i j : ι) :
    (LinearMap.toMatrix (realSchurOrthogonalJoinBasis P u v).toBasis
      (realSchurOrthogonalJoinBasis P u v).toBasis f) (Sum.inl i) (Sum.inl j) =
      (LinearMap.toMatrix u.toBasis u.toBasis (f.restrict hP)) i j := by
  let b := realSchurOrthogonalJoinBasis P u v
  change (LinearMap.toMatrix b.toBasis b.toBasis f) (Sum.inl i) (Sum.inl j)=_
  rw [LinearMap.toMatrix_apply,LinearMap.toMatrix_apply]
  rw [b.coe_toBasis_repr_apply,u.coe_toBasis_repr_apply]
  rw [OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply]
  simp only [OrthonormalBasis.coe_toBasis]
  rw [realSchurOrthogonalJoinBasis_inl,realSchurOrthogonalJoinBasis_inl]
  rfl

#print axioms realSchurOrthogonalJoinBasis_upperLeft_eq
end SpectralRadiusUpperTail
