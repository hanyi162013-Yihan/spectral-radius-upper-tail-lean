import SpectralRadiusUpperTail.PowerSpectrumExclusion
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- A finite geometric identity bounds the actual inverse; no infinite-series
norm estimate is assumed. -/
lemma inverse_one_sub_norm_of_power {R : Type*} [NormedRing R] [NormOneClass R]
    (x : R) (m : ℕ) (hu : IsUnit (1-x)) (hp : ‖x^m‖ ≤ 1/2) :
    ‖Ring.inverse (1-x)‖ ≤ 2*∑ j ∈ Finset.range m, ‖x‖^j := by
  let B := Ring.inverse (1-x)
  have hi : (1-x)*B = 1 := Ring.mul_inverse_cancel _ hu
  have he := congrArg (fun y : R => y*B) (geom_sum_mul_neg x m)
  rw [mul_assoc, hi, mul_one, sub_mul, one_mul] at he
  have hr : B = (∑ j ∈ Finset.range m, x^j)+x^m*B := by rw [he]; abel
  have hs : ‖∑ j ∈ Finset.range m, x^j‖ ≤ ∑ j ∈ Finset.range m, ‖x‖^j :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_pow_le x j))
  have ht := norm_add_le (∑ j ∈ Finset.range m, x^j) (x^m*B)
  rw [← hr] at ht
  have hm := norm_mul_le (x^m) B
  have hc := mul_le_mul_of_nonneg_right hp (norm_nonneg B)
  change ‖B‖ ≤ _
  nlinarith

/-- The finite-power hypothesis also proves invertibility in a complete normed algebra. -/
lemma inverse_one_sub_power_bound {𝕂 R : Type*} [NontriviallyNormedField 𝕂]
    [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] [NormOneClass R]
    (x : R) (m : ℕ) (hp : ‖x^m‖ ≤ 1/2) :
    IsUnit (1-x) ∧ ‖Ring.inverse (1-x)‖ ≤ 2*∑ j ∈ Finset.range m, ‖x‖^j := by
  have hz : (1 : 𝕂) ∈ resolventSet 𝕂 x :=
    mem_resolventSet_of_power_norm x 1 m (by simpa using (show ‖x^m‖ < 1 by linarith))
  have hu : IsUnit (1-x) := by
    simpa using (spectrum.mem_resolventSet_iff.mp hz)
  exact ⟨hu, inverse_one_sub_norm_of_power x m hu hp⟩

#print axioms inverse_one_sub_norm_of_power
#print axioms inverse_one_sub_power_bound
end SpectralRadiusUpperTail
