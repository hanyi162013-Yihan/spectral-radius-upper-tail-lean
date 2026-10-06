import SpectralRadiusUpperTail.TiltedEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- A locally small logarithmic perturbation preserves a uniform entry
square-exponential moment after normalization. -/
theorem log_density_squareExp (μ : Measure E) [IsProbabilityMeasure μ]
    (D : E → ℝ) (hD : Measurable D) (d : ℝ) (hd : 0 < d)
    (hlog : ∀ x, |D x| ≤ d*(‖x‖+‖x‖^2))
    (hexp : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ)
    (hZhalf : 1/2 ≤ ∫ x, Real.exp (D x) ∂μ) :
    let Z := ∫ x, Real.exp (D x) ∂μ
    let ν := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (D x)/Z))
    IsProbabilityMeasure ν ∧
      Integrable (fun x : E => Real.exp (d*‖x‖^2)) ν ∧
      (∫ x : E, Real.exp (d*‖x‖^2) ∂ν) ≤
        2*Real.exp d*(∫ x : E, Real.exp (4*d*‖x‖^2) ∂μ) := by
  let Z := ∫ x, Real.exp (D x) ∂μ
  let k := fun x => Real.exp (D x)/Z
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) hZhalf
  have hZi : Z⁻¹ ≤ 2 := by
    have h : 1/Z ≤ 2 := (div_le_iff₀ hZ).mpr (by linarith)
    simpa only [one_div] using h
  have hp (x : E) : Real.exp (D x)*Real.exp (d*‖x‖^2) ≤
      Real.exp d*Real.exp (4*d*‖x‖^2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (le_abs_self (D x)).trans (hlog x)
    have hn := mul_le_mul_of_nonneg_left
      (show ‖x‖ ≤ 1+‖x‖^2 by nlinarith [sq_nonneg (‖x‖-1)]) hd.le
    have hs := mul_nonneg hd.le (sq_nonneg ‖x‖)
    nlinarith
  have hgi : Integrable (fun x => Real.exp (D x)) μ := by
    apply (hexp.const_mul (Real.exp d)).mono_nonneg (Real.measurable_exp.comp hD).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
    · apply Filter.Eventually.of_forall
      intro x
      apply le_trans _ (hp x)
      have h1 : 1 ≤ Real.exp (d*‖x‖^2) := Real.one_le_exp_iff.mpr (by positivity)
      simpa only [mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg (D x))
  have hk : Measurable k := (Real.measurable_exp.comp hD).div_const Z
  have hkn (x : E) : 0 ≤ k x := div_nonneg (Real.exp_nonneg _) hZ.le
  have hki : Integrable k μ := hgi.div_const Z
  have hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hkn)]
    change ENNReal.ofReal (∫ x, Real.exp (D x)/Z ∂μ) = 1
    rw [integral_div, show (∫ x, Real.exp (D x) ∂μ) = Z from rfl,
      div_self (ne_of_gt hZ), ENNReal.ofReal_one]
  have hkp (x : E) : k x*Real.exp (d*‖x‖^2) ≤
      (2*Real.exp d)*Real.exp (4*d*‖x‖^2) := by
    have h := mul_le_mul hZi (hp x)
      (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = Z⁻¹*(Real.exp (D x)*Real.exp (d*‖x‖^2)) := by dsimp [k]; ring
      _ ≤ 2*(Real.exp d*Real.exp (4*d*‖x‖^2)) := h
      _ = _ := by ring
  have hkfi : Integrable (fun x => k x*Real.exp (d*‖x‖^2)) μ := by
    apply (hexp.const_mul (2*Real.exp d)).mono_nonneg
      (hk.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => mul_nonneg (hkn x) (Real.exp_nonneg _))
    · exact Filter.Eventually.of_forall hkp
  refine ⟨normalizedDensity_probability μ _ hnorm, ?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hkn _), smul_eq_mul] using hkfi
  · rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hkn _), smul_eq_mul]
    have h := integral_mono hkfi (hexp.const_mul (2*Real.exp d)) hkp
    simpa only [integral_const_mul] using h

#print axioms log_density_squareExp
end SpectralRadiusUpperTail
