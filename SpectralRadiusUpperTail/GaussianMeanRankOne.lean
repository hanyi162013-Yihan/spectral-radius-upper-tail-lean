import SpectralRadiusUpperTail.ActualMatrixIdentity

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

noncomputable def rankOneTiltTarget (η : ℝ) (b : 𝕂) (v : ℕ → 𝕂) (i : Fin n) : 𝕂 :=
  ((Real.sqrt (n : ℝ)*(η+1) : ℝ) : 𝕂)*(b*v i.val)

lemma gaussianMeanMatrix_rankOne (η : ℝ) (hη : 0 < η) (b : 𝕂) (v : ℕ → 𝕂)
    (hn : 0 < n) (hv : (∑ i : Fin n, ‖v i.val‖^2) = 1) :
    gaussianMeanMatrix v (rankOneTiltTarget η b v) η =
      b • Matrix.vecMulVec (fun i : Fin n => v i.val) (star (fun i : Fin n => v i.val)) := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hs' : (Real.sqrt (n : ℝ) : 𝕂) ≠ 0 := by exact_mod_cast hs
  have he : ((η+1 : ℝ) : 𝕂) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < η+1))
  ext i j
  simp only [gaussianMeanMatrix,rankOneTiltTarget,hv,Matrix.smul_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul,RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_div,RCLike.ofReal_one,RCLike.ofReal_mul]
  field_simp

#print axioms rankOneTiltTarget
#print axioms gaussianMeanMatrix_rankOne
end SpectralRadiusUpperTail
