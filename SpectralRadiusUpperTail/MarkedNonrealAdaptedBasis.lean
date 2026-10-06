import SpectralRadiusUpperTail.MarkedNonrealCoordinates
import SpectralRadiusUpperTail.RealSchurOrthogonalRestrictionBlock
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

namespace SpectralRadiusUpperTail

/-- Adapt an orthonormal basis to a prescribed invariant plane, retaining
the characteristic polynomial of that particular plane as the first block. -/
theorem exists_markedNonreal_adapted_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ)
    (hdim : Module.finrank ℝ E=m+2)
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : Module.finrank ℝ P=2) (hInv : ∀ x ∈ P, f x ∈ P) :
    ∃ b : OrthonormalBasis (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ E,
      realSchurMixedLowerProjection (markedNonrealBlockSizes m)
        (LinearMap.toMatrix b.toBasis b.toBasis f)=0 ∧
      (markedNonrealFirstBlock m (LinearMap.toMatrix b.toBasis b.toBasis f)).charpoly =
        (f.restrict hInv).charpoly := by
  have hperp : Module.finrank ℝ Pᗮ=m := by
    have hsum := P.finrank_add_finrank_orthogonal
    omega
  let u := (stdOrthonormalBasis ℝ P).reindex (finCongr hP)
  let v := (stdOrthonormalBasis ℝ Pᗮ).reindex (finCongr hperp)
  let q := realSchurOrthogonalJoinBasis P u v
  let e := markedNonrealCoordEquiv m
  let b := q.reindex e
  have hentry (i j : Fin 2 ⊕ Fin m) :
      (LinearMap.toMatrix b.toBasis b.toBasis f) (e i) (e j) =
        (LinearMap.toMatrix q.toBasis q.toBasis f) i j := by
    rw [LinearMap.toMatrix_apply,LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.coe_toBasis]
    simp only [b,OrthonormalBasis.repr_reindex,OrthonormalBasis.reindex_apply,
      Equiv.symm_apply_apply]
  refine ⟨b,?_,?_⟩
  · apply (markedNonreal_lower_zero_iff m _).mpr
    intro i j
    change (LinearMap.toMatrix b.toBasis b.toBasis f) (e (.inr i)) (e (.inl j))=0
    rw [hentry]
    exact realSchurOrthogonalJoinBasis_lowerLeft_zero f P hInv u v i j
  · have hmat : markedNonrealFirstBlock m (LinearMap.toMatrix b.toBasis b.toBasis f) =
        LinearMap.toMatrix u.toBasis u.toBasis (f.restrict hInv) := by
      ext i j
      change (LinearMap.toMatrix b.toBasis b.toBasis f) (e (.inl i)) (e (.inl j))=_
      rw [hentry]
      exact realSchurOrthogonalJoinBasis_upperLeft_eq f P hInv u v i j
    rw [hmat,(f.restrict hInv).charpoly_toMatrix]

#print axioms exists_markedNonreal_adapted_basis
end SpectralRadiusUpperTail
