import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- An intertwining linear map also intertwines every polynomial in the
two endomorphisms. This is the algebraic bridge from a block-upper
matrix to its invariant first block and quotient. -/
theorem aeval_intertwining_apply
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] E) (g : F →ₗ[ℝ] F) (L : E →ₗ[ℝ] F)
    (h : ∀ x : E, L (f x) = g (L x))
    (p : ℝ[X]) (x : E) :
    L (aeval f p x) = aeval g p (L x) := by
  have hpow (k : ℕ) : ∀ y : E,
      L ((f^k) y) = (g^k) (L y) := by
    induction k with
    | zero => intro y; simp
    | succ k ih =>
        intro y
        rw [pow_succ, Module.End.mul_apply,
          ih (f y), h y, pow_succ, Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, L.map_add, hp, hq]
  | monomial k a =>
      simp only [aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, L.map_smul]
      rw [hpow k x]

#print axioms aeval_intertwining_apply
end SpectralRadiusUpperTail
