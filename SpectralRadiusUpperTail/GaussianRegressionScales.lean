import SpectralRadiusUpperTail.SmallCoefficientThreshold
import SpectralRadiusUpperTail.RegressionTailLimit

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Choose the cutoff first and the coefficient threshold second. The choices
are independent of the dimension, coefficient vector and bounded target. -/
theorem exists_gaussian_regression_scales (μ : Measure 𝕂)
    (a d η K : ℝ) (ha : 0 < a) (hd : 0 < d) (C : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ δ : ℝ, 0 < δ ∧
      gaussianGlobalScoreConstant μ a d*δ^2 < d ∧
      (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*δ^2 <
        (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8 ∧
      (C R)^2*δ^2+gaussianRowRegressionTailBound μ a d η K R < ε := by
  obtain ⟨R, hR, htail⟩ := exists_gaussianRowRegression_cutoff μ a d η K hd (ε/2) (by positivity)
  have hc := rowSquareExpExponent_pos (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)
    (by positivity) (integral_nonneg (fun _ => Real.exp_nonneg _))
  obtain ⟨δ, hδ, h₁, h₂, h₃⟩ := exists_pos_three_square_bounds
    (gaussianGlobalScoreConstant μ a d) (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))
    ((C R)^2) d ((rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8) (ε/2)
    (gaussianGlobalScoreConstant_nonneg μ a d ha) (by positivity) (sq_nonneg _) hd
    (by positivity) (by positivity)
  exact ⟨R, hR, δ, hδ, h₁, h₂, by linarith⟩

/-- Transfer the uniform coefficient cutoff to every actual coordinate. -/
lemma gaussian_regression_coefficient_thresholds (μ : Measure 𝕂)
    (a d δ : ℝ) (ha : 0 < a) (hd : 0 < d) (hδ : 0 ≤ δ)
    (h₁ : gaussianGlobalScoreConstant μ a d*δ^2 < d)
    (h₂ : (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*δ^2 <
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8)
    (b : 𝕂) (hb : ‖b‖ ≤ δ) :
    gaussianGlobalScoreConstant μ a d*‖b‖^2 ≤ d ∧
      (4*((gaussianGlobalScoreConstant μ a d)^2/(4*d)+1))*‖b‖^2 ≤
        (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/8 := by
  have hs := (sq_le_sq₀ (norm_nonneg b) hδ).mpr hb
  exact ⟨(mul_le_mul_of_nonneg_left hs (gaussianGlobalScoreConstant_nonneg μ a d ha)).trans h₁.le,
    (mul_le_mul_of_nonneg_left hs (by positivity)).trans h₂.le⟩

#print axioms exists_gaussian_regression_scales
#print axioms gaussian_regression_coefficient_thresholds
end SpectralRadiusUpperTail
