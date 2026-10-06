import SpectralRadiusUpperTail.GaussianMeanRankOne

namespace SpectralRadiusUpperTail
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

noncomputable def spectralTiltTarget (b : 𝕂) (v : ℕ → 𝕂) (i : Fin n) : 𝕂 :=
  (Real.sqrt (n : ℝ) : 𝕂)*(b*v i.val)

lemma rankOneTiltTarget_reparametrize (η : ℝ) (hη : 0 < η) (b : 𝕂) (v : ℕ → 𝕂) :
    rankOneTiltTarget (n := n) η (b/((η+1 : ℝ) : 𝕂)) v = spectralTiltTarget b v := by
  have he : ((η+1 : ℝ) : 𝕂) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < η+1))
  funext i
  simp only [rankOneTiltTarget,spectralTiltTarget,RCLike.ofReal_mul]
  field_simp

#print axioms spectralTiltTarget
#print axioms rankOneTiltTarget_reparametrize
end SpectralRadiusUpperTail
