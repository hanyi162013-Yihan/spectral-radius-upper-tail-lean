import SpectralRadiusUpperTail.RealSchurPolynomialFlagUniqueness
import SpectralRadiusUpperTail.RealSchurSubspaceAnnihilator
import SpectralRadiusUpperTail.RealSchurQuotientAnnihilator
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- An invariant subspace with coprime restricted and quotient
characteristic polynomials is the canonical polynomial kernel of its
restricted characteristic polynomial. -/
theorem invariantSubmodule_eq_restrictCharpoly_kernel
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hInv : ∀ x : E, x ∈ P → f x ∈ P)
    (hcop : IsCoprime (f.restrict hInv).charpoly
      (realLinearMapInvariantQuotient f P hInv).charpoly) :
    P = LinearMap.ker (aeval f (f.restrict hInv).charpoly) := by
  exact invariantSubmodule_eq_ker_aeval_of_coprime f P
    (f.restrict hInv).charpoly
    (realLinearMapInvariantQuotient f P hInv).charpoly
    hcop hInv
    (fun x hx => invariantSubmodule_charpoly_aeval_eq_zero f P hInv x hx)
    (fun x => invariantQuotient_charpoly_aeval_mem f P hInv x)

/-- Two invariant first-block flags with the same characteristic
polynomial coincide when each is spectrally separated from its quotient. -/
theorem invariantSubmodule_unique_of_restrictCharpoly_eq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P Q : Submodule ℝ E)
    (hP : ∀ x : E, x ∈ P → f x ∈ P)
    (hQ : ∀ x : E, x ∈ Q → f x ∈ Q)
    (hcopP : IsCoprime (f.restrict hP).charpoly
      (realLinearMapInvariantQuotient f P hP).charpoly)
    (hcopQ : IsCoprime (f.restrict hQ).charpoly
      (realLinearMapInvariantQuotient f Q hQ).charpoly)
    (heq : (f.restrict hP).charpoly = (f.restrict hQ).charpoly) :
    P = Q := by
  calc
    P = LinearMap.ker (aeval f (f.restrict hP).charpoly) :=
      invariantSubmodule_eq_restrictCharpoly_kernel f P hP hcopP
    _ = LinearMap.ker (aeval f (f.restrict hQ).charpoly) := by rw [heq]
    _ = Q := (invariantSubmodule_eq_restrictCharpoly_kernel f Q hQ hcopQ).symm

#print axioms invariantSubmodule_eq_restrictCharpoly_kernel
#print axioms invariantSubmodule_unique_of_restrictCharpoly_eq
end SpectralRadiusUpperTail
