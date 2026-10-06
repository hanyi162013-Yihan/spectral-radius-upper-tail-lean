import SpectralRadiusUpperTail.IidPowerBilinearIntegral
import Mathlib.Algebra.Algebra.Operations

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
variable {n k : ℕ}

noncomputable def normalizedPowerBilinear (p q : Fin n → 𝕂) (k : ℕ)
    (y : Fin n × Fin n → 𝕂) : 𝕂 :=
  ∑ i, star (p i) *
    ((((1 / Real.sqrt (n : ℝ) : ℝ) : 𝕂) • Matrix.of (fun i j => y (i,j)))^k).mulVec q i

lemma matrixPowerBilinear_smul (A : Matrix (Fin n) (Fin n) 𝕂)
    (p q : Fin n → 𝕂) (s : 𝕂) (k : ℕ) :
    (∑ i, star (p i) * ((s • A)^k).mulVec q i) =
      s^k * (∑ i, star (p i) * (A^k).mulVec q i) := by
  rw [smul_pow, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma normalizedPowerBilinear_norm_sq (p q : Fin n → 𝕂) (k : ℕ)
    (y : Fin n × Fin n → 𝕂) :
    ‖normalizedPowerBilinear p q k y‖^2 =
      (1/(n : ℝ))^k * ‖∑ i, star (p i) *
        ((Matrix.of (fun i j => y (i,j)))^k).mulVec q i‖^2 := by
  unfold normalizedPowerBilinear
  rw [matrixPowerBilinear_smul]
  simp only [norm_mul, norm_pow, RCLike.norm_ofReal, mul_pow]
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs, div_pow,
    one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma inverse_power_cancellation (hn : 0 < n) (hk : 0 < k) (C : ℝ) :
    (1/(n : ℝ))^k * (C*(n : ℝ)^(k-1)) = C/(n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_one, pow_succ, one_div, inv_pow]
  have hpow : (n : ℝ)^j ≠ 0 := pow_ne_zero _ hn0
  field_simp
  <;> ring

#print axioms normalizedPowerBilinear
#print axioms matrixPowerBilinear_smul
#print axioms normalizedPowerBilinear_norm_sq
#print axioms inverse_power_cancellation
end SpectralRadiusUpperTail
