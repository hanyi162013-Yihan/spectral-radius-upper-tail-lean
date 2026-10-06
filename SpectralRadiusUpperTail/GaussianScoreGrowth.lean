import SpectralRadiusUpperTail.GaussianScore

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma energy_bound_to_linear_growth (a c L r m : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (h : m^2 ≤ ((1+r^2)/a+L)/c) :
    m ≤ Real.sqrt ((1/a+L)/c) * (1+r) := by
  have hcoef : 0 ≤ 1/a+L := add_nonneg (div_nonneg zero_le_one ha.le) hL
  have hD : 0 ≤ (1/a+L)/c := div_nonneg hcoef hc.le
  have hnum : (1+r^2)/a+L ≤ (1/a+L)*(1+r)^2 := by
    calc
      _ = (1/a+L)*(1+r^2)-L*r^2 := by ring
      _ ≤ (1/a+L)*(1+r^2) := sub_le_self _ (mul_nonneg hL (sq_nonneg r))
      _ ≤ (1/a+L)*(1+r)^2 := mul_le_mul_of_nonneg_left (by nlinarith) hcoef
  have hbound : ((1+r^2)/a+L)/c ≤ ((1/a+L)/c)*(1+r)^2 := by
    calc
      _ ≤ ((1/a+L)*(1+r)^2)/c := div_le_div_of_nonneg_right hnum hc.le
      _ = _ := by ring
  have hsq := Real.sq_sqrt hD
  have hnon : 0 ≤ Real.sqrt ((1/a+L)/c)*(1+r) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hsqbound : m^2 ≤ (Real.sqrt ((1/a+L)/c)*(1+r))^2 := by
    rw [mul_pow, hsq]
    exact h.trans hbound
  nlinarith

theorem gaussianSoftTilt_mean_growth (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ Real.exp L) (s : E) :
    ‖∫ x : E, x ∂gaussianSoftTilt μ a s‖ ≤ Real.sqrt ((1/a+L)/c)*(1+‖s‖) :=
  energy_bound_to_linear_growth a c L ‖s‖ _ ha hc hLn (norm_nonneg _) (norm_nonneg _)
    (gaussianSoftTilt_mean_sq μ hX hm hvar a c L ha hc hexp hL s)

noncomputable def gaussianScoreConstant (a c L : ℝ) : ℝ :=
  (2/a)*(1+Real.sqrt ((1/a+L)/c))

/-- The logarithmic Gaussian score has an explicit uniform linear growth bound. -/
theorem gaussian_log_score_growth (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (hm : (∫ x : E, x ∂μ) = 0)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) ≤ 1) (a c L : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hLn : 0 ≤ L)
    (hexp : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ)
    (hL : (∫ x : E, Real.exp (c*‖x‖^2) ∂μ) ≤ Real.exp L) :
    0 ≤ gaussianScoreConstant a c L ∧ ∀ s : E,
      HasFDerivAt (fun t => Real.log (gaussianConvolution μ a t))
        ((-2/a) • innerSL ℝ (s-∫ x : E, x ∂gaussianSoftTilt μ a s)) s ∧
      ‖(-2/a) • innerSL ℝ (s-∫ x : E, x ∂gaussianSoftTilt μ a s)‖ ≤
        gaussianScoreConstant a c L*(1+‖s‖) := by
  let B := Real.sqrt ((1/a+L)/c)
  change 0 ≤ (2/a)*(1+B) ∧ _
  refine ⟨mul_nonneg (div_nonneg (by norm_num) ha.le)
    (by dsimp [B]; positivity), ?_⟩
  intro s
  refine ⟨gaussian_log_score μ hX hm a ha s, ?_⟩
  have hmean := gaussianSoftTilt_mean_growth μ hX hm hvar a c L ha hc hLn hexp hL s
  have hcoef : |(-2/a : ℝ)| = 2/a := by norm_num [abs_div, abs_of_pos ha]
  rw [norm_smul, Real.norm_eq_abs, hcoef, innerSL_apply_norm]
  calc
    _ ≤ (2/a)*(‖s‖+‖∫ x : E, x ∂gaussianSoftTilt μ a s‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (div_nonneg (by norm_num) ha.le)
    _ ≤ (2/a)*((1+B)*(1+‖s‖)) :=
      mul_le_mul_of_nonneg_left (by dsimp [B]; nlinarith only [hmean])
        (div_nonneg (by norm_num) ha.le)
    _ = _ := by dsimp [gaussianScoreConstant, B]; ring

#print axioms gaussian_log_score_growth
end SpectralRadiusUpperTail
