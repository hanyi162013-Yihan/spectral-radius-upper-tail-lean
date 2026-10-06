import SpectralRadiusUpperTail.IidPositiveSphereMoment
import SpectralRadiusUpperTail.ENNExponentialRatio

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma iid_complex_opNorm_tail (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (hXi : Integrable (fun x : ℂ => x) μ)
    (hm : (∫ x : ℂ, x ∂μ) = 0) (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (R : ℝ) (hR : 0 ≤ R) :
    let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
    (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
      {x | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ≤
        2*Real.exp ((n : ℝ)*(Real.log 2+2-c*R^2/2)) := by
  let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
  have hc : 0 < c := (iid_row_squareExp μ (fun _ : Fin 0 => (0 : ℂ)) hXi hm
    (by simp) τ hτ hexp).1
  let P := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))
  let T := ENNReal.ofReal (Real.exp ((n : ℝ)*(c*R^2/2-2)-Real.log 2))
  have hT : T ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hset : {x : Fin n → Fin n → ℂ | R < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖} ⊆
      {x | T ≤ complexSpherePositiveMoment n c (Matrix.of x)} := by
    intro x hx
    have hsq : (n : ℝ)*R^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.of x)‖^2 := by
      have hs : R^2 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedArray x)‖^2 :=
        pow_le_pow_left₀ hR hx.le 2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hh := mul_le_mul_of_nonneg_left hs hn0.le
      rw [normalizedArray_opNorm_square n hn x] at hh
      exact hh
    have hw := complex_sphere_positive_norm_witness n hn c hc.le (Matrix.of x)
    apply le_trans ?_ hw
    have he : T = (1/2 : ℝ≥0∞)*ENNReal.ofReal (Real.exp ((n : ℝ)*(c*R^2/2-2))) := by
      dsimp [T]
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp [div_eq_mul_inv, mul_comm]
    rw [he]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
  have hmark := (mul_le_mul' (le_refl T) (measure_mono (μ := P) hset)).trans
    (mul_meas_ge_le_lintegral (μ := P) (positive_sphere_moment_measurable n hn c) T)
  have hb := hmark.trans (iid_positive_sphere_moment μ n hn hXi hm τ hτ hexp)
  have hinv := mul_le_mul' (le_refl T⁻¹) hb
  rw [ENNReal.inv_mul_cancel_left hT ENNReal.ofReal_ne_top] at hinv
  have he2 : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he2] at hinv
  change _ ≤ (ENNReal.ofReal (Real.exp _))⁻¹*ENNReal.ofReal (Real.exp _) at hinv
  rw [ennreal_exp_ratio] at hinv
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hinv
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at ht
  convert! ht using 1
  calc
    2*Real.exp ((n : ℝ)*(Real.log 2+2-c*R^2/2)) =
        Real.exp (Real.log 2+(n : ℝ)*(Real.log 2+2-c*R^2/2)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = _ := by congr 1; ring

#print axioms iid_complex_opNorm_tail
end SpectralRadiusUpperTail
