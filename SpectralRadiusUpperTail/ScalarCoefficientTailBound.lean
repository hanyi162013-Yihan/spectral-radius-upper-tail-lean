import SpectralRadiusUpperTail.MatrixCoefficient
import SpectralRadiusUpperTail.ResolventFiniteExpansion

namespace SpectralRadiusUpperTail
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma matrixCoefficient_sum {ι : Type*} (s : Finset ι) (p q : Fin n → ℂ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    matrixCoefficient p q (∑ i ∈ s, A i) = ∑ i ∈ s, matrixCoefficient p q (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [matrixCoefficient]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,matrixCoefficient_add,ih]

lemma matrixCoefficient_resolvent_expansion (p q : Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hz : z ≠ 0)
    (hu : z ∈ resolventSet ℂ A) (k : ℕ) :
    matrixCoefficient p q (resolvent A z) =
      (∑ j ∈ Finset.range k, (z⁻¹)^(j+1) * matrixCoefficient p q (A^j)) +
        (z⁻¹)^k * matrixCoefficient p q (A^k*resolvent A z) := by
  conv_lhs => rw [resolvent_finite_expansion A z hz hu k]
  rw [matrixCoefficient_add,matrixCoefficient_sum,matrixCoefficient_smul]
  simp only [matrixCoefficient_smul]

lemma matrixCoefficient_remainder_bound (p q : Fin n → ℂ)
    (hp : (∑ i, ‖p i‖^2) ≤ 1) (hq : (∑ i, ‖q i‖^2) ≤ 1)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (k : ℕ) (r P C : ℝ)
    (hr : 0 < r) (hz : r ≤ ‖z‖)
    (hP : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A^k)‖ ≤ P)
    (hC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (resolvent A z)‖ ≤ C) :
    ‖(z⁻¹)^k * matrixCoefficient p q (A^k*resolvent A z)‖ ≤ P*C/r^k := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans hP
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have hb := (matrixCoefficient_norm_le p q hp hq (A^k*resolvent A z)).trans
    ((Matrix.l2_opNorm_mul (A^k) (resolvent A z)).trans
      (mul_le_mul hP hC (norm_nonneg _) hP0))
  rw [norm_mul,norm_pow,norm_inv,inv_pow]
  calc
    _ ≤ (‖z‖^k)⁻¹*(P*C) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = P*C/‖z‖^k := by ring
    _ ≤ P*C/r^k := div_le_div_of_nonneg_left (mul_nonneg hP0 hC0)
      (pow_pos hr _) (pow_le_pow_left₀ hr.le hz _)

#print axioms matrixCoefficient_sum
#print axioms matrixCoefficient_resolvent_expansion
#print axioms matrixCoefficient_remainder_bound
end SpectralRadiusUpperTail
