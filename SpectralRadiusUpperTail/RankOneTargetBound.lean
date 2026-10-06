import SpectralRadiusUpperTail.GaussianMeanRankOne

namespace SpectralRadiusUpperTail
variable {𝕂 : Type*} [RCLike 𝕂]

lemma rankOneTiltTarget_bound {n : ℕ} (η : ℝ) (hη : 0 < η) (b : 𝕂)
    (v : ℕ → 𝕂) (L : ℝ) (hflat : ∀ i : Fin n, ‖v i.val‖ ≤ L/Real.sqrt (n : ℝ))
    (i : Fin n) : ‖rankOneTiltTarget η b v i‖ ≤ (η+1)*‖b‖*L := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hv : Real.sqrt (n : ℝ)*‖v i.val‖ ≤ L := by
    simpa only [mul_comm] using (le_div_iff₀ hs).1 (hflat i)
  have hh := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ (η+1)*‖b‖)
  simpa only [rankOneTiltTarget,norm_mul,RCLike.norm_ofReal,
    abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ)*(η+1))] using
    (show (Real.sqrt (n : ℝ)*(η+1))*(‖b‖*‖v i.val‖) ≤ (η+1)*‖b‖*L by nlinarith [hh])

#print axioms rankOneTiltTarget_bound
end SpectralRadiusUpperTail
