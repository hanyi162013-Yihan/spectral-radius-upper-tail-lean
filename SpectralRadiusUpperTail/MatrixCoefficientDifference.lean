import SpectralRadiusUpperTail.MatrixCoefficient

namespace SpectralRadiusUpperTail
open scoped BigOperators
variable {n : ℕ}

lemma matrixCoefficient_sub (p q : Fin n → ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    matrixCoefficient p q (A-B) = matrixCoefficient p q A - matrixCoefficient p q B := by
  simp only [matrixCoefficient,map_sub,ContinuousLinearMap.sub_apply,inner_sub_right]

lemma matrixCoefficient_difference_le (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixCoefficient p q A-matrixCoefficient p q B‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A-B)‖ := by
  rw [← matrixCoefficient_sub]
  exact matrixCoefficient_norm_le p q hp hq (A-B)

#print axioms matrixCoefficient_sub
#print axioms matrixCoefficient_difference_le
end SpectralRadiusUpperTail
