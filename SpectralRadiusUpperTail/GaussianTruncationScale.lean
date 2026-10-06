import SpectralRadiusUpperTail.GaussianLocalTruncation
import SpectralRadiusUpperTail.LocalCoefficientSmallness

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def gaussianLocalMomentCost (μ : Measure 𝕂) (d : ℝ) : ℝ :=
  ∫ x : 𝕂, (1+‖x‖^2)*(d*(‖x‖+‖x‖^2))*Real.exp (d*(‖x‖+‖x‖^2)) ∂μ

noncomputable def gaussianTruncationScale (μ : Measure 𝕂) (a d K : ℝ) : ℝ :=
  gaussianScoreConstant a
    (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)*(K+2)/d

noncomputable def gaussianErrorExpBound (μ : Measure 𝕂) (d : ℝ) : ℝ :=
  ((2*Real.exp d*(∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)+
    (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))/2)^2

lemma gaussianLocalMomentCost_nonneg (μ : Measure 𝕂) (d : ℝ) (hd : 0 ≤ d) :
    0 ≤ gaussianLocalMomentCost μ d := by
  apply integral_nonneg
  intro x
  positivity

lemma gaussianTruncationScale_nonneg (μ : Measure 𝕂) (a d K : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hK : 0 ≤ K) : 0 ≤ gaussianTruncationScale μ a d K := by
  unfold gaussianTruncationScale gaussianScoreConstant
  positivity

#print axioms gaussianTruncationScale_nonneg
end SpectralRadiusUpperTail
