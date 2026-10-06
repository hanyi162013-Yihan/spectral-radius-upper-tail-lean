import SpectralRadiusUpperTail.RealSchurOrthogonalJoinBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped InnerProductSpace

/-- The lower-right operator after orthogonal splitting along `P`.
For an invariant `P`, this is the quotient endomorphism written in
the orthogonal complement coordinates. -/
noncomputable def realSchurOrthogonalCompression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E) : Pᗮ →ₗ[ℝ] Pᗮ :=
  ((Pᗮ).orthogonalProjectionOnto).toLinearMap.comp
    (f.comp (Pᗮ).subtype)

@[simp] theorem realSchurOrthogonalCompression_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E) (x : Pᗮ) :
    realSchurOrthogonalCompression f P x =
      (Pᗮ).orthogonalProjectionOnto (f (x : E)) := rfl

/-- The lower-left matrix block vanishes in any joined orthonormal
basis when the leading subspace is invariant. -/
theorem realSchurOrthogonalJoinBasis_lowerLeft_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (u : OrthonormalBasis ι ℝ P)
    (v : OrthonormalBasis κ ℝ Pᗮ)
    (i : κ) (j : ι) :
    (LinearMap.toMatrix
      (realSchurOrthogonalJoinBasis P u v).toBasis
      (realSchurOrthogonalJoinBasis P u v).toBasis f)
        (Sum.inr i) (Sum.inl j) = 0 := by
  let b := realSchurOrthogonalJoinBasis P u v
  have hleft : b (Sum.inl j) ∈ P := by
    rw [realSchurOrthogonalJoinBasis_inl]
    exact (u j).property
  have hright : b (Sum.inr i) ∈ Pᗮ := by
    rw [realSchurOrthogonalJoinBasis_inr]
    exact (v i).property
  change (LinearMap.toMatrix b.toBasis b.toBasis f) (Sum.inr i) (Sum.inl j) = 0
  rw [LinearMap.toMatrix_apply]
  rw [b.coe_toBasis_repr_apply]
  change b.repr (f (b (Sum.inl j))) (Sum.inr i) = 0
  rw [OrthonormalBasis.repr_apply_apply]
  exact Submodule.inner_left_of_mem_orthogonal (hP _ hleft) hright

/-- The lower-right matrix block is exactly the matrix of the
orthogonal compression to `Pᗮ`. -/
theorem realSchurOrthogonalJoinBasis_lowerRight_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (u : OrthonormalBasis ι ℝ P)
    (v : OrthonormalBasis κ ℝ Pᗮ)
    (i j : κ) :
    (LinearMap.toMatrix
      (realSchurOrthogonalJoinBasis P u v).toBasis
      (realSchurOrthogonalJoinBasis P u v).toBasis f)
        (Sum.inr i) (Sum.inr j) =
      (LinearMap.toMatrix v.toBasis v.toBasis
        (realSchurOrthogonalCompression f P)) i j := by
  let b := realSchurOrthogonalJoinBasis P u v
  change (LinearMap.toMatrix b.toBasis b.toBasis f)
      (Sum.inr i) (Sum.inr j) = _
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [b.coe_toBasis_repr_apply, v.coe_toBasis_repr_apply]
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  simp only [OrthonormalBasis.coe_toBasis]
  have hj : b (Sum.inr j) = (v j : E) :=
    realSchurOrthogonalJoinBasis_inr P u v j
  rw [hj]
  have hi : b (Sum.inr i) = (v i : E) :=
    realSchurOrthogonalJoinBasis_inr P u v i
  rw [hi, realSchurOrthogonalCompression_apply]
  change ⟪(v i : E), f (v j : E)⟫_ℝ =
    ⟪v i, (Pᗮ).orthogonalProjectionOnto (f (v j : E))⟫_ℝ
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (v i)
    (f (v j : E))).symm

#print axioms realSchurOrthogonalCompression_apply
#print axioms realSchurOrthogonalJoinBasis_lowerLeft_zero
#print axioms realSchurOrthogonalJoinBasis_lowerRight_eq
end SpectralRadiusUpperTail
