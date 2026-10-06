import SpectralRadiusUpperTail.RealSchurPolynomialIntertwining
import SpectralRadiusUpperTail.RealSchurInvariantQuotient
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- The characteristic polynomial of an invariant quotient sends the
whole space into the invariant subspace. This is the trailing-block
annihilation condition used to identify an ordered Schur flag. -/
theorem invariantQuotient_charpoly_aeval_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hInv : ∀ x : E, x ∈ P → f x ∈ P)
    (x : E) :
    aeval f (realLinearMapInvariantQuotient f P hInv).charpoly x ∈ P := by
  let g := realLinearMapInvariantQuotient f P hInv
  have hinter := aeval_intertwining_apply f g P.mkQ
    (fun y => realLinearMapInvariantQuotient_mkQ f P hInv y)
    g.charpoly x
  have hg : aeval g g.charpoly = 0 := LinearMap.aeval_self_charpoly g
  have hzero : P.mkQ (aeval f g.charpoly x) = 0 := by
    rw [hinter, hg]
    rfl
  exact (Submodule.Quotient.mk_eq_zero P).mp
    (by simpa only [Submodule.mkQ_apply] using hzero)

#print axioms invariantQuotient_charpoly_aeval_mem
end SpectralRadiusUpperTail
