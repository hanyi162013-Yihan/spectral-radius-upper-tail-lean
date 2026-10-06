import SpectralRadiusUpperTail.GaussianHermitianProcess
import SpectralRadiusUpperTail.GaussianLogarithmicCutoff

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped MeasureTheory BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- The deterministic variance envelope of the actual Hermitian process
vanishes at the logarithmic cutoff and flat coefficient scale. -/
theorem gaussianHermitianVarianceEnvelope_tendsto (μ : Measure 𝕂) (a d A L : ℝ) :
    Tendsto (fun n : ℕ =>
      (12*gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*
        gaussianLocalMomentCost μ d)*(L/Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
  have hh := (affine_sqrt_log_flat_tendsto A L 2).const_mul
    ((12*gaussianScoreConstant a
      (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)*
      gaussianLocalMomentCost μ d)/d)
  convert! hh using 1
  · funext n
    unfold gaussianTruncationScale
    ring
  · ring

/-- The actual serialized predictable variance has this deterministic
bound eventually. Only the original entry assumptions and coefficient
flatness are inputs; neither a matrix variance bound nor smallness is assumed. -/
theorem gaussianHermitianPredictableVariance_eventually_le
    (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (4*d*‖x‖^2)) μ)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n)
    (v : ℕ → ℕ → 𝕂) (hv : ∀ n, ∑ j : Fin n, ‖v n j.val‖^2 ≤ 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (t : (n : ℕ) → Fin n → 𝕂) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂gaussianSequentialMatrixLaw μ (v n) a (t n),
      ‖Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := 𝕂)
        (gaussianHermitianPredictableVariance μ (v n) a (t n)
          (A*Real.sqrt (Real.log (n : ℝ))) (R n) (n*n) x)‖ ≤
      (12*gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*
        gaussianLocalMomentCost μ d)*(L/Real.sqrt (n : ℝ)) := by
  filter_upwards [gaussianLogarithmicCutoff_smallness μ a d A L] with n hn
  have hh := gaussianHermitianVarianceSum_operator_le μ hX hm hvar (v n) (hv n)
    a d ha hd hexp (t n) (A*Real.sqrt (Real.log (n : ℝ))) (L/Real.sqrt (n : ℝ))
    (R n) (mul_nonneg hA (Real.sqrt_nonneg _))
    (div_nonneg hL (Real.sqrt_nonneg _)) hn.1 (hR n) (hflat n) hn.2.1 hn.2.2
  simpa only [gaussianHermitianPredictableVariance_terminal] using hh

#print axioms gaussianHermitianPredictableVariance_eventually_le
end SpectralRadiusUpperTail
