import SpectralRadiusUpperTail.GaussianRowRegressionMoment

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma rowSquareExpExponent_pos (τ M : ℝ) (hτ : 0 < τ) (hM : 0 ≤ M) :
    0 < rowSquareExpExponent τ M := by
  have hC := (squareExpMgfConstant_pos τ M hτ hM).le
  unfold rowSquareExpExponent
  positivity

omit [BorelSpace 𝕂] [SecondCountableTopology 𝕂] in
lemma gaussianGlobalScoreConstant_nonneg (μ : Measure 𝕂) (a d : ℝ) (ha : 0 < a) :
    0 ≤ gaussianGlobalScoreConstant μ a d := by
  unfold gaussianGlobalScoreConstant gaussianScoreConstant
  positivity

/-- The actual dimension-independent noncompact error tends to zero with
the cutoff. All other parameters remain fixed. -/
theorem gaussianRowRegressionTailBound_tendsto (μ : Measure 𝕂)
    (a d η K : ℝ) (hd : 0 < d) :
    Tendsto (gaussianRowRegressionTailBound μ a d η K) atTop (𝓝 0) := by
  let c := rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
  have hc : 0 < c := rowSquareExpExponent_pos _ _ (by positivity)
    (integral_nonneg (fun _ => Real.exp_nonneg _))
  have hp : Tendsto (fun R : ℝ => (c/4)*R^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (by positivity)
  have he : Tendsto (fun R : ℝ => Real.exp (-(c/4)*R^2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hp
  have hh := (he.const_mul
    ((4*((gaussianGlobalMeanConstant μ a d)^2+1/η^2))*(Real.exp (c/8)*(1+8/c)))).mul_const
      (2*Real.exp ((K^2+1)/a+c*K^2))
  convert! hh using 1 <;> simp only [mul_zero, zero_mul, gaussianRowRegressionTailBound, c]

lemma exists_gaussianRowRegression_cutoff (μ : Measure 𝕂)
    (a d η K : ℝ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ gaussianRowRegressionTailBound μ a d η K R < ε := by
  have he := (gaussianRowRegressionTailBound_tendsto μ a d η K hd).eventually (Iio_mem_nhds hε)
  exact ((eventually_ge_atTop (0 : ℝ)).and he).exists

#print axioms gaussianRowRegressionTailBound_tendsto
#print axioms exists_gaussianRowRegression_cutoff
end SpectralRadiusUpperTail
