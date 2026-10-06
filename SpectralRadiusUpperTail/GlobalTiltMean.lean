import SpectralRadiusUpperTail.GlobalLogEnvelope
import SpectralRadiusUpperTail.LogDensitySquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Centeredness makes the actual exponentially weighted first moment small,
with an envelope valid for every nonnegative perturbation size u. -/
theorem global_tilt_numerator (μ : Measure E) [IsProbabilityMeasure μ]
    (D : E → ℝ) (hDm : Measurable D) (C u e d : ℝ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (heu : e ≤ u)
    (hd : 0 < d) (hsmall : C*e ≤ d)
    (hD : ∀ x, |D x| ≤ C*u*‖x‖+C*e*‖x‖^2)
    (hm : (∫ x : E, x ∂μ) = 0)
    (hexp : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    Integrable (fun x : E => Real.exp (D x) • x) μ ∧
      ‖∫ x : E, Real.exp (D x) • x ∂μ‖ ≤
        C*u*Real.exp (C^2*u^2/(4*d))*
          (∫ x : E, (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2) ∂μ) := by
  let F := fun x : E => (Real.exp (D x)-1) • x
  let W := fun x : E => (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2)
  let A := C*u*Real.exp (C^2*u^2/(4*d))
  have hW : Integrable W μ := squareExp_regression_weight_integrable μ d hd hexp
  have hb (x : E) : ‖F x‖ ≤ A*W x := by
    dsimp [F, A, W]
    rw [norm_smul, Real.norm_eq_abs, mul_comm |Real.exp (D x)-1|]
    exact global_exp_variation_weight C u e d ‖x‖ (D x) hC hu he heu hd (norm_nonneg x) hsmall (hD x)
  have hF : Integrable F μ := (hW.const_mul A).mono' (by
    exact (((Real.measurable_exp.comp hDm).sub measurable_const).smul measurable_id).aestronglyMeasurable)
    (Filter.Eventually.of_forall hb)
  have hi : Integrable (fun x : E => x) μ := by
    have hn := squareExp_norm_pow_integrable μ (4*d) (by positivity) hexp 1
    apply hn.mono' (by fun_prop)
    apply Filter.Eventually.of_forall
    intro x
    convert! (le_rfl : ‖x‖ ≤ ‖x‖) using 1 <;> simp only [pow_one]
  have heq (x : E) : Real.exp (D x) • x = F x+x := by dsimp [F]; rw [sub_smul, one_smul]; abel
  have hnum : Integrable (fun x : E => Real.exp (D x) • x) μ := by
    simp_rw [heq]
    exact hF.add hi
  have hmean : (∫ x : E, Real.exp (D x) • x ∂μ) = ∫ x, F x ∂μ := by
    simp_rw [heq]
    rw [integral_add hF hi, hm, add_zero]
  refine ⟨hnum, ?_⟩
  rw [hmean]
  apply (norm_integral_le_integral_norm F).trans
  have hh := integral_mono hF.norm (hW.const_mul A) hb
  simpa only [integral_const_mul] using hh

/-- The normalized exponential tilt is an actual probability law, with an
integrable Bochner mean and a global quantitative bound on that mean. -/
theorem global_tilt_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (D : E → ℝ) (hDm : Measurable D) (C u e d : ℝ)
    (hC : 0 ≤ C) (hu : 0 ≤ u) (he : 0 ≤ e) (heu : e ≤ u)
    (hd : 0 < d) (hsmall : C*e ≤ d)
    (hD : ∀ x, |D x| ≤ C*u*‖x‖+C*e*‖x‖^2)
    (hm : (∫ x : E, x ∂μ) = 0) (hvar : (∫ x : E, ‖x‖^2 ∂μ) = 1)
    (hexp : Integrable (fun x : E => Real.exp (4*d*‖x‖^2)) μ) :
    let Z := ∫ x, Real.exp (D x) ∂μ
    let ν := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (D x)/Z))
    IsProbabilityMeasure ν ∧ Integrable (fun x : E => x) ν ∧
      ‖∫ x : E, x ∂ν‖ ≤
        (C*(∫ x : E, (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2) ∂μ)*Real.exp (9*C^2))*
          u*Real.exp ((C^2/(4*d)+1)*u^2) := by
  let Z := ∫ x, Real.exp (D x) ∂μ
  let k := fun x => Real.exp (D x)/Z
  let M := ∫ x : E, (‖x‖^2+‖x‖^3)*Real.exp (2*d*‖x‖^2) ∂μ
  have hM : 0 ≤ M := integral_nonneg (fun x => by positivity)
  have hlow := global_log_normalizer_lower μ D hDm C u e d hC hu he heu hd hsmall hD hvar hexp
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hlow
  have hgi := global_log_exp_integrable μ D hDm C u e d hC hu he hd hsmall hD hexp
  obtain ⟨hnum, hnb⟩ := global_tilt_numerator μ D hDm C u e d hC hu he heu hd hsmall hD hm hexp
  have hk : Measurable k := (Real.measurable_exp.comp hDm).div_const Z
  have hkn (x : E) : 0 ≤ k x := div_nonneg (Real.exp_nonneg _) hZ.le
  have hki : Integrable k μ := hgi.div_const Z
  have hnorm : (∫⁻ x, ENNReal.ofReal (k x) ∂μ) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hki (Filter.Eventually.of_forall hkn)]
    change ENNReal.ofReal (∫ x, Real.exp (D x)/Z ∂μ) = 1
    rw [integral_div, show (∫ x, Real.exp (D x) ∂μ) = Z from rfl,
      div_self hZ.ne', ENNReal.ofReal_one]
  have hsmul (x : E) : k x • x = Z⁻¹ • (Real.exp (D x) • x) := by
    rw [smul_smul]
    congr 1
    dsimp [k]
    ring
  have hweighted : Integrable (fun x : E => k x • x) μ := by
    simp_rw [hsmul]
    exact hnum.smul Z⁻¹
  refine ⟨normalizedDensity_probability μ _ hnorm, ?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [ENNReal.toReal_ofReal (hkn _)] using hweighted
  · rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hkn _)]
    change ‖∫ x : E, k x • x ∂μ‖ ≤ _
    simp_rw [hsmul]
    rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hZ.le)]
    have hinv : Z⁻¹ ≤ Real.exp (3*C*u) := by
      have hh : 1/Z ≤ 1/Real.exp (-3*C*u) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hlow
      simpa only [one_div, Real.exp_neg, inv_inv, neg_mul] using hh
    have hex : Real.exp (3*C*u)*Real.exp (C^2*u^2/(4*d)) ≤
        Real.exp (9*C^2)*Real.exp ((C^2/(4*d)+1)*u^2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh : 3*C*u ≤ 9*C^2+u^2 := by nlinarith [sq_nonneg (u-3*C)]
      have heq : 9*C^2+(C^2/(4*d)+1)*u^2 = 9*C^2+u^2+C^2*u^2/(4*d) := by ring
      rw [heq]
      exact add_le_add hh le_rfl
    calc
      _ ≤ Real.exp (3*C*u)*(C*u*Real.exp (C^2*u^2/(4*d))*M) :=
        mul_le_mul hinv hnb (norm_nonneg _) (Real.exp_nonneg _)
      _ = (C*M*u)*(Real.exp (3*C*u)*Real.exp (C^2*u^2/(4*d))) := by ring
      _ ≤ (C*M*u)*(Real.exp (9*C^2)*Real.exp ((C^2/(4*d)+1)*u^2)) :=
        mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := by dsimp [M]; ring

#print axioms global_tilt_mean
end SpectralRadiusUpperTail
