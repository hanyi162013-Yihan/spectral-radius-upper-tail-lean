import SpectralRadiusUpperTail.RealSchurOrthogonalSplitBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- In the orthonormal basis obtained from `P ⊕ Pᗮ`, invariance of
`P` makes every entry of the lower-left matrix block vanish. -/
theorem realSchurOrthogonalSplitBasis_lowerLeft_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P)
    (i : Fin (Module.finrank ℝ Pᗮ))
    (j : Fin (Module.finrank ℝ P)) :
    (LinearMap.toMatrix
      (realSchurOrthogonalSplitBasis P).toBasis
      (realSchurOrthogonalSplitBasis P).toBasis f)
        (Sum.inr i) (Sum.inl j) = 0 := by
  let b := realSchurOrthogonalSplitBasis P
  have hleft : b (Sum.inl j) ∈ P :=
    realSchurOrthogonalSplitBasis_inl_mem P j
  have hright : b (Sum.inr i) ∈ Pᗮ :=
    realSchurOrthogonalSplitBasis_inr_mem P i
  change (LinearMap.toMatrix b.toBasis b.toBasis f) (Sum.inr i) (Sum.inl j) = 0
  rw [LinearMap.toMatrix_apply]
  rw [b.coe_toBasis_repr_apply]
  change b.repr (f (b (Sum.inl j))) (Sum.inr i) = 0
  rw [OrthonormalBasis.repr_apply_apply]
  exact Submodule.inner_left_of_mem_orthogonal (hP _ hleft) hright

#print axioms realSchurOrthogonalSplitBasis_lowerLeft_zero
end SpectralRadiusUpperTail
