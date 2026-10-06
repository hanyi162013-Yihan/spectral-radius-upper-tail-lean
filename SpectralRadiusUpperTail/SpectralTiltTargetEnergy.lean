import SpectralRadiusUpperTail.SpectralTiltTarget

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma spectralTiltTarget_energy (b : 𝕂) (v : ℕ → 𝕂)
    (hv : (∑ i : Fin n, ‖v i.val‖^2) = 1) :
    (∑ i : Fin n, ‖spectralTiltTarget b v i‖^2) = (n : ℝ)*‖b‖^2 := by
  simp only [spectralTiltTarget,norm_mul,RCLike.norm_ofReal,mul_pow,sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg n),← Finset.mul_sum,← mul_assoc,hv,mul_one]

lemma spectralTiltTarget_bound (b : 𝕂) (v : ℕ → 𝕂) (L : ℝ)
    (hflat : ∀ i : Fin n, ‖v i.val‖ ≤ L/Real.sqrt (n : ℝ)) (i : Fin n) :
    ‖spectralTiltTarget b v i‖ ≤ ‖b‖*L := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hv : Real.sqrt (n : ℝ)*‖v i.val‖ ≤ L := by
    simpa only [mul_comm] using (le_div_iff₀ hs).1 (hflat i)
  have hh := mul_le_mul_of_nonneg_left hv (norm_nonneg b)
  simpa only [spectralTiltTarget,norm_mul,RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_assoc,mul_comm,mul_left_comm] using hh

#print axioms spectralTiltTarget_energy
#print axioms spectralTiltTarget_bound
end SpectralRadiusUpperTail
