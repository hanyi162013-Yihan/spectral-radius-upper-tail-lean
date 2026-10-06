import SpectralRadiusUpperTail.RealSchurPolynomialIntertwining
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- The characteristic polynomial of an invariant first block
annihilates every vector in that block. -/
theorem invariantSubmodule_charpoly_aeval_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hInv : ∀ x : E, x ∈ P → f x ∈ P)
    (x : E) (hx : x ∈ P) :
    aeval f (f.restrict hInv).charpoly x = 0 := by
  let g : P →ₗ[ℝ] P := f.restrict hInv
  have hinter := aeval_intertwining_apply g f P.subtype
    (fun y => by rfl) g.charpoly ⟨x,hx⟩
  have hg : aeval g g.charpoly = 0 := LinearMap.aeval_self_charpoly g
  rw [hg] at hinter
  simpa [g] using hinter.symm

#print axioms invariantSubmodule_charpoly_aeval_eq_zero
end SpectralRadiusUpperTail
