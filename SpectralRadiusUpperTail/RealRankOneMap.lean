import SpectralRadiusUpperTail.GaussianMeanRankOne

namespace SpectralRadiusUpperTail
open scoped Matrix

lemma real_rankOne_map {n : ℕ} (b : ℝ) (v : Fin n → ℝ) :
    (b • Matrix.vecMulVec v v).map Complex.ofRealHom =
      (b : ℂ) • Matrix.vecMulVec (fun i => (v i : ℂ)) (star (fun i => (v i : ℂ))) := by
  ext i j
  simp [Matrix.map_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply]

#print axioms real_rankOne_map
end SpectralRadiusUpperTail
