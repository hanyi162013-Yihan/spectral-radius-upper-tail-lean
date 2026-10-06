import SpectralRadiusUpperTail.RealArrayGaussianDensity
import SpectralRadiusUpperTail.GaussianProductDensity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

theorem standardNormal_finite_eq_normalizedTilt {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => standardNormal)=
      normalizedTilt volume
        (fun a : ι → ℝ => ENNReal.ofReal (Real.exp (-(1/2)*∑ i, (a i)^2))) := by
  simp_rw [realArrayGaussianWeight_prod (1 : ℝ)]
  rw [volume_pi,pi_normalizedTilt_ofReal
    (fun _ : ι => (volume : Measure ℝ)) (fun _ x => Real.exp (-(1/2 : ℝ)*x^2))
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => integral_exp_pos (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)))]
  simp only [← standardNormal_eq_normalizedTilt]

theorem finiteGaussian_raw_lintegral {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a, ENNReal.ofReal (Real.exp (-(∑ i, (a i)^2)/2))*F a)=
      (∫⁻ a : ι → ℝ, ENNReal.ofReal (Real.exp (-(∑ i, (a i)^2)/2)))*
        ∫⁻ a, F a ∂Measure.pi (fun _ : ι => standardNormal) := by
  let w := fun a : ι → ℝ => ENNReal.ofReal (Real.exp (-(1/2)*∑ i, (a i)^2))
  have hw : Measurable w := by fun_prop
  have he (a : ι → ℝ) : ENNReal.ofReal (Real.exp (-(∑ i, (a i)^2)/2))=w a := by
    dsimp [w]
    congr 2
    ring
  simp_rw [he]
  have hi := realArrayGaussianWeight_integrable (ι := ι) 1 (by norm_num)
  have hz : (∫⁻ a, w a) = ENNReal.ofReal (∫ a : ι → ℝ, Real.exp (-(1/2)*∑ i, (a i)^2)) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
      (fun _ => (Real.exp_pos _).le))).symm
  have hz0 : (∫⁻ a, w a) ≠ 0 := by
    rw [hz]
    exact (ENNReal.ofReal_pos.mpr (integral_exp_pos hi)).ne'
  have hzt : (∫⁻ a, w a) ≠ ∞ := by rw [hz]; exact ENNReal.ofReal_ne_top
  rw [standardNormal_finite_eq_normalizedTilt,normalizedTilt]
  rw [lintegral_withDensity_eq_lintegral_mul _ (hw.div_const _) hF]
  change (∫⁻ a, w a*F a)=(∫⁻ a, w a)*∫⁻ a, (w a/(∫⁻ b, w b))*F a
  simp_rw [div_eq_mul_inv]
  have he' (a : ι → ℝ) : w a*(∫⁻ b, w b)⁻¹*F a=(∫⁻ b, w b)⁻¹*(w a*F a) := by ac_rfl
  simp_rw [he']
  rw [lintegral_const_mul' _ (fun a : ι → ℝ => w a*F a) (ENNReal.inv_ne_top.mpr hz0),
    ← mul_assoc,ENNReal.mul_inv_cancel hz0 hzt,one_mul]

#print axioms standardNormal_finite_eq_normalizedTilt
#print axioms finiteGaussian_raw_lintegral
end SpectralRadiusUpperTail
