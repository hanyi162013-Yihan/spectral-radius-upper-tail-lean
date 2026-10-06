import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- A spectral flag is determined by its first-block annihilating
polynomial when the complementary polynomial is coprime. The two
annihilation hypotheses are the form supplied by a block-upper matrix
and its trailing quotient. -/
theorem invariantSubmodule_eq_ker_aeval_of_coprime
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (p q : ℝ[X]) (hpq : IsCoprime p q)
    (hInv : ∀ x : E, x ∈ P → f x ∈ P)
    (hPann : ∀ x : E, x ∈ P → aeval f p x = 0)
    (hqrange : ∀ x : E, aeval f q x ∈ P) :
    P = LinearMap.ker (aeval f p) := by
  apply le_antisymm
  · intro x hx
    exact LinearMap.mem_ker.mpr (hPann x hx)
  · intro x hx
    rcases hpq with ⟨a,b,hbez⟩
    have hzero : aeval f (a*p) x = 0 := by
      rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.mp hx, map_zero]
    have hmem : aeval f (b*q) x ∈ P := by
      rw [aeval_mul, Module.End.mul_apply]
      exact Polynomial.aeval_apply_smul_mem_of_le_comap
        (hqrange x) b f hInv
    have hsum : aeval f (a*p) x + aeval f (b*q) x = x := by
      calc
        _ = aeval f (a*p+b*q) x := by rw [map_add, LinearMap.add_apply]
        _ = x := by simp [hbez]
    rw [hzero, zero_add] at hsum
    exact hsum ▸ hmem

#print axioms invariantSubmodule_eq_ker_aeval_of_coprime
end SpectralRadiusUpperTail
