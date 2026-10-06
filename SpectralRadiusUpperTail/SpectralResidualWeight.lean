import SpectralRadiusUpperTail.GaussianMatrixWeight
import SpectralRadiusUpperTail.SpectralTiltTargetEnergy
import SpectralRadiusUpperTail.ActualMatrixIdentity
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace SpectralRadiusUpperTail
open WithLp
open scoped BigOperators Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

lemma normalizedArray_mulVec_row (x : Fin n → Fin n → 𝕂) (v : Fin n → 𝕂) (i : Fin n) :
    ((normalizedArray x).mulVec v) i =
      (Real.sqrt (n : ℝ) : 𝕂)⁻¹*(∑ j, v j*x i j) := by
  simp only [Matrix.mulVec,dotProduct,normalizedArray,RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_div,RCLike.ofReal_one,one_div,RCLike.ofReal_inv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma spectralTiltTarget_residual (x : Fin n → Fin n → 𝕂) (v : Fin n → 𝕂)
    (b : 𝕂) (i : Fin n) :
    spectralTiltTarget b (zeroExtendVector v) i-∑ j, v j*x i j =
      -((Real.sqrt (n : ℝ) : 𝕂)*((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec v) i) := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hs' : (Real.sqrt (n : ℝ) : 𝕂) ≠ 0 := by exact_mod_cast hs
  simp only [spectralTiltTarget,zeroExtendVector_fin,Matrix.sub_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    normalizedArray_mulVec_row]
  simp only [mul_sub,← mul_assoc,mul_inv_cancel₀ hs',one_mul]
  ring

lemma spectralTiltTarget_residual_energy (x : Fin n → Fin n → 𝕂) (v : Fin n → 𝕂) (b : 𝕂) :
    (∑ i, ‖spectralTiltTarget b (zeroExtendVector v) i-∑ j, v j*x i j‖^2) =
      (n : ℝ)*‖toLp 2 ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec v)‖^2 := by
  simp_rw [spectralTiltTarget_residual,norm_neg,norm_mul,mul_pow,RCLike.norm_ofReal,
    sq_abs,Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq]

lemma gaussianMatrixWeight_spectral (a : ℝ) (b : 𝕂) (v : Fin n → 𝕂)
    (x : Fin n → Fin n → 𝕂) :
    gaussianMatrixWeight a v (spectralTiltTarget b (zeroExtendVector v)) x =
      Real.exp (-(n : ℝ)*‖toLp 2
        ((normalizedArray x-b • (1 : Matrix (Fin n) (Fin n) 𝕂)).mulVec v)‖^2/a) := by
  rw [gaussianMatrixWeight,spectralTiltTarget_residual_energy,neg_mul]

#print axioms normalizedArray_mulVec_row
#print axioms spectralTiltTarget_residual
#print axioms spectralTiltTarget_residual_energy
#print axioms gaussianMatrixWeight_spectral
end SpectralRadiusUpperTail
