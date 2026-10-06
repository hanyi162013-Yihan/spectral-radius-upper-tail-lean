import SpectralRadiusUpperTail.ResolventFiniteExpansion

namespace SpectralRadiusUpperTail

lemma resolvent_mul_element {𝕂 R : Type*} [CommRing 𝕂] [Ring R] [Algebra 𝕂 R]
    (a : R) (z : 𝕂) (hz : z ∈ resolventSet 𝕂 a) :
    resolvent a z*a = z • resolvent a z-1 := by
  have hi : resolvent a z*(algebraMap 𝕂 R z-a) = 1 :=
    Ring.inverse_mul_cancel _ (spectrum.mem_resolventSet_iff.mp hz)
  rw [mul_sub,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one] at hi
  calc
    _ = z • resolvent a z-(z • resolvent a z-resolvent a z*a) := by abel
    _ = _ := by rw [hi]

#print axioms resolvent_mul_element
end SpectralRadiusUpperTail
