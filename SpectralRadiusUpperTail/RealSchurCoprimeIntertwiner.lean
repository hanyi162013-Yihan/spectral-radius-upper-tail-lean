import SpectralRadiusUpperTail.RealSchurPolynomialIntertwining
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- A linear map intertwining finite-dimensional endomorphisms with
coprime characteristic polynomials must vanish. -/
theorem linearMap_eq_zero_of_coprime_charpoly_intertwining
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗ[ℝ] E) (g : F →ₗ[ℝ] F) (L : E →ₗ[ℝ] F)
    (hcop : IsCoprime f.charpoly g.charpoly)
    (hinter : ∀ x : E, L (f x) = g (L x)) :
    L = 0 := by
  ext x
  obtain ⟨a,b,hbez⟩ := hcop
  have hf : aeval g f.charpoly (L x) = 0 := by
    rw [← aeval_intertwining_apply f g L hinter]
    rw [LinearMap.aeval_self_charpoly f]
    simp
  have hg : aeval g g.charpoly (L x) = 0 := by
    rw [LinearMap.aeval_self_charpoly g]
    rfl
  have hsum : aeval g (a*f.charpoly+b*g.charpoly) (L x) = 0 := by
    rw [map_add, LinearMap.add_apply, aeval_mul, aeval_mul,
      Module.End.mul_apply, Module.End.mul_apply, hf, hg]
    simp
  rw [hbez] at hsum
  simpa using hsum

#print axioms linearMap_eq_zero_of_coprime_charpoly_intertwining
end SpectralRadiusUpperTail
