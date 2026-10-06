import SpectralRadiusUpperTail.RealSchurOrthogonalCompression
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The quotient class of a vector is represented in orthogonal
coordinates by its projection onto the orthogonal complement. -/
theorem realSchur_quotientEquivOrthogonal_mkQ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (x : E) :
    P.quotientEquivOrthogonal (P.mkQ x) =
      (Pᗮ).orthogonalProjectionOnto x := by
  let q := (Pᗮ).orthogonalProjectionOnto x
  have hxq : P.mkQ x = P.mkQ (q : E) := by
    apply (Submodule.Quotient.eq P).mpr
    have hp : x - (q : E) = (P.orthogonalProjectionOnto x : E) := by
      change x - ((Pᗮ).orthogonalProjectionOnto x : E) = _
      rw [P.orthogonalProjectionOnto_orthogonal]
      simp
    rw [hp]
    exact (P.orthogonalProjectionOnto x).property
  rw [hxq]
  exact P.quotientEquivOrthogonal_mk (q : E) q.property

/-- The quotient recursion and the orthogonal-complement recursion
are the same endomorphism in two coordinate systems. -/
theorem realSchur_quotientMap_orthogonalCompression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P) (x : Pᗮ) :
    P.quotientEquivOrthogonal
      (realLinearMapInvariantQuotient f P hP
        (P.quotientEquivOrthogonal.symm x)) =
      realSchurOrthogonalCompression f P x := by
  have hs : P.quotientEquivOrthogonal.symm x = P.mkQ (x : E) := by
    exact P.quotientEquivOrthogonal_symm_eq_mk (x : E) x.property
  rw [hs, realLinearMapInvariantQuotient_mkQ,
    realSchur_quotientEquivOrthogonal_mkQ]
  rfl

#print axioms realSchur_quotientMap_orthogonalCompression
end SpectralRadiusUpperTail
