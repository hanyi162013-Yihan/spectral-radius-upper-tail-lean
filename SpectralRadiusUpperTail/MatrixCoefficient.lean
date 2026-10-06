import SpectralRadiusUpperTail.MatrixOperatorComparison
import SpectralRadiusUpperTail.NormalizedPowerBilinear

namespace SpectralRadiusUpperTail
open scoped BigOperators
open WithLp
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

noncomputable def matrixCoefficient (p q : Fin n → 𝕂) (A : Matrix (Fin n) (Fin n) 𝕂) : 𝕂 :=
  inner 𝕂 (toLp 2 p) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A (toLp 2 q))

lemma matrixCoefficient_eq_sum (p q : Fin n → 𝕂) (A : Matrix (Fin n) (Fin n) 𝕂) :
    matrixCoefficient p q A = ∑ i, star (p i)*(A.mulVec q) i := by
  simp only [matrixCoefficient,Matrix.toEuclideanCLM_toLp,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply,mul_comm]

lemma matrixCoefficient_add (p q : Fin n → 𝕂) (A B : Matrix (Fin n) (Fin n) 𝕂) :
    matrixCoefficient p q (A+B) = matrixCoefficient p q A + matrixCoefficient p q B := by
  simp only [matrixCoefficient,map_add,ContinuousLinearMap.add_apply,inner_add_right]

lemma matrixCoefficient_smul (p q : Fin n → 𝕂) (s : 𝕂) (A : Matrix (Fin n) (Fin n) 𝕂) :
    matrixCoefficient p q (s • A) = s * matrixCoefficient p q A := by
  simp only [matrixCoefficient,map_smul,ContinuousLinearMap.smul_apply,inner_smul_right]

lemma euclidean_norm_le_one_of_energy (p : Fin n → 𝕂) (hp : (∑ i, ‖p i‖^2) ≤ 1) :
    ‖toLp 2 p‖ ≤ 1 := by
  have he := EuclideanSpace.norm_sq_eq (toLp 2 p)
  change ‖toLp 2 p‖^2 = ∑ i, ‖p i‖^2 at he
  nlinarith [norm_nonneg (toLp 2 p)]

lemma matrixCoefficient_norm_le (p q : Fin n → 𝕂)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (A : Matrix (Fin n) (Fin n) 𝕂) :
    ‖matrixCoefficient p q A‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖ := by
  have hp1 := euclidean_norm_le_one_of_energy p hp
  have hq1 := euclidean_norm_le_one_of_energy q hq
  have hh := norm_inner_le_norm (𝕜 := 𝕂) (toLp 2 p) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A (toLp 2 q))
  have hv := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A).le_opNorm (toLp 2 q)
  have ha : 0 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A‖ := norm_nonneg _
  have hqv := mul_le_mul_of_nonneg_left hq1 ha
  have hpv := mul_le_mul_of_nonneg_right hp1
    (norm_nonneg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := 𝕂) A (toLp 2 q)))
  change ‖inner 𝕂 _ _‖ ≤ _
  nlinarith

#print axioms matrixCoefficient
#print axioms matrixCoefficient_eq_sum
#print axioms matrixCoefficient_add
#print axioms matrixCoefficient_smul
#print axioms euclidean_norm_le_one_of_energy
#print axioms matrixCoefficient_norm_le
end SpectralRadiusUpperTail
