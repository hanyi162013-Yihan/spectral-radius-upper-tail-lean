import SpectralRadiusUpperTail.GramPatternGeometricBound

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

noncomputable def gramDefectPolynomialConstant (μ : Measure 𝕂) (c : ℝ) (m : ℕ) : ℝ :=
  (64*(2*(m : ℝ)+1))^72 *
    (max 1 (2*∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ) * ((2*(m : ℝ)+1)*(1+1/c)))^6

lemma gramDefectRatio_le_polynomial (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c)
    (m q n : ℕ) (hq : 1 ≤ q) :
    gramDefectRatio μ c m q n ≤ gramDefectPolynomialConstant μ c m * (q : ℝ)^78 / n := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlen : 2*((q : ℝ)*m)+1 ≤ (2*(m : ℝ)+1)*q := by nlinarith
  have hmax : 0 ≤ max 1 (2*∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hc' : 0 ≤ 1+1/c := by positivity
  unfold gramDefectRatio
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hb : (gramDefectCountBase m q : ℝ) ≤ (64*(2*(m : ℝ)+1))^72*(q : ℝ)^72 := by
    unfold gramDefectCountBase
    push_cast
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have ha : signedWordMomentBase μ c (2*(q*m)) ≤
      (max 1 (2*∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ) * ((2*(m : ℝ)+1)*(1+1/c))) * q := by
    unfold signedWordMomentBase
    push_cast
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hlen hc') hmax
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  have ha0 : 0 ≤ signedWordMomentBase μ c (2*(q*m)) :=
    (by norm_num : (0:ℝ) ≤ 1).trans (signedWordMomentBase_one_le μ c hc _)
  have hh := mul_le_mul hb (pow_le_pow_left₀ ha0 ha 6) (by positivity) (by positivity)
  convert hh using 1
  unfold gramDefectPolynomialConstant
  rw [mul_pow]
  have he : (q : ℝ)^78 = (q : ℝ)^72*(q : ℝ)^6 := by rw [← pow_add]
  rw [he]
  ring

#print axioms gramDefectPolynomialConstant
#print axioms gramDefectRatio_le_polynomial
end SpectralRadiusUpperTail
