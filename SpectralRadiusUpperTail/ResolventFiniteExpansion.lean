import SpectralRadiusUpperTail.UniformPowerResolvent

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma resolvent_finite_expansion {𝕂 R : Type*} [Field 𝕂] [Ring R] [Algebra 𝕂 R]
    (a : R) (z : 𝕂) (hz : z ≠ 0) (hu : z ∈ resolventSet 𝕂 a) (k : ℕ) :
    resolvent a z = (∑ j ∈ Finset.range k, (z⁻¹)^(j+1) • a^j) +
      (z⁻¹)^k • (a^k * resolvent a z) := by
  have hi : (algebraMap 𝕂 R z-a)*resolvent a z = 1 :=
    Ring.mul_inverse_cancel _ (spectrum.mem_resolventSet_iff.mp hu)
  have he : 1-z⁻¹ • a = z⁻¹ • (algebraMap 𝕂 R z-a) := by
    rw [smul_sub,Algebra.algebraMap_eq_smul_one,smul_smul,inv_mul_cancel₀ hz,one_smul]
  have hx : (1-z⁻¹ • a)*resolvent a z = z⁻¹ • (1 : R) := by
    rw [he,smul_mul_assoc,hi]
  have hh := congrArg (fun t : R => t*resolvent a z) (geom_sum_mul_neg (z⁻¹ • a) k)
  rw [mul_assoc,hx,mul_smul_comm,mul_one,sub_mul,one_mul] at hh
  have hs : z⁻¹ • (∑ j ∈ Finset.range k, (z⁻¹ • a)^j) =
      ∑ j ∈ Finset.range k, (z⁻¹)^(j+1) • a^j := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_pow,smul_smul,pow_succ']
  rw [hs,smul_pow,smul_mul_assoc] at hh
  rw [hh]
  abel

#print axioms resolvent_finite_expansion
end SpectralRadiusUpperTail
