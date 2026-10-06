import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Algebra.Spectrum.Basic

namespace SpectralRadiusUpperTail

/-- Neumann perturbation with the actual inverse norm, without normality. -/
lemma isUnit_sub_of_inverse_norm {R : Type*} [NormedRing R] [CompleteSpace R]
    (u : Rˣ) (e : R) (h : ‖((u⁻¹ : Rˣ) : R)‖*‖e‖ < 1) :
    IsUnit ((u : R)-e) := by
  have hh := u.isUnit.mul (isUnit_one_sub_of_norm_lt_one
    ((norm_mul_le ((u⁻¹ : Rˣ) : R) e).trans_lt h))
  have hu : (u : R)*((u⁻¹ : Rˣ) : R) = 1 := u.val_inv
  simpa only [mul_sub, mul_one, ← mul_assoc, hu, one_mul] using hh

/-- A point of the actual resolvent stays outside the perturbed spectrum
when the inverse-norm times the perturbation norm is less than one. -/
lemma mem_resolventSet_add_of_norm {𝕂 R : Type*} [CommRing 𝕂]
    [NormedRing R] [CompleteSpace R] [Algebra 𝕂 R]
    (a e : R) (z : 𝕂) (hz : z ∈ resolventSet 𝕂 a)
    (h : ‖Ring.inverse (algebraMap 𝕂 R z-a)‖*‖e‖ < 1) :
    z ∈ resolventSet 𝕂 (a+e) := by
  obtain ⟨u, hu⟩ := (spectrum.mem_resolventSet_iff).mp hz
  rw [← hu, Ring.inverse_unit] at h
  apply (spectrum.mem_resolventSet_iff).mpr
  rw [← sub_sub, ← hu]
  exact isUnit_sub_of_inverse_norm u e h

#print axioms isUnit_sub_of_inverse_norm
#print axioms mem_resolventSet_add_of_norm
end SpectralRadiusUpperTail
