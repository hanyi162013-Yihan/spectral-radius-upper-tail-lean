import SpectralRadiusUpperTail.LogarithmicCutoff
import SpectralRadiusUpperTail.GaussianStoppedErrorBound
import SpectralRadiusUpperTail.GaussianMatrixStopping

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- All coefficient-smallness hypotheses hold eventually for the actual
logarithmic safe cutoff and flat coefficient envelope. -/
lemma gaussianLogarithmicCutoff_smallness (μ : Measure 𝕂) (a d A L : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      L/Real.sqrt (n : ℝ) ≤ 1 ∧
      gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*(L/Real.sqrt (n : ℝ)) ≤ 1 ∧
      (gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*(L/Real.sqrt (n : ℝ)))*
        gaussianLocalMomentCost μ d ≤ 1/2 := by
  have hflat : Tendsto (fun n : ℕ => L/Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ =>
      gaussianTruncationScale μ a d (A*Real.sqrt (Real.log (n : ℝ)))*(L/Real.sqrt (n : ℝ)))
      atTop (𝓝 0) := by
    have hh := (affine_sqrt_log_flat_tendsto A L 2).const_mul
      (gaussianScoreConstant a
        (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ)) (Real.log 2)/d)
    convert! hh using 1
    · funext n
      unfold gaussianTruncationScale
      ring
    · ring
  have he := hs.mul_const (gaussianLocalMomentCost μ d)
  simp only [zero_mul] at he
  filter_upwards [hflat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))] with n hn hs' he'
  exact ⟨hn.le, hs'.le, he'.le⟩

/-- The discarded second moment has any polynomial decay permitted by the
strict cutoff exponent. Taking m=2 yields the manuscript's o(1/n) bound. -/
theorem gaussianTruncationTail_logarithmic_tendsto (μ : Measure 𝕂)
    (d B : ℝ) (m : ℕ) (h : (m : ℝ) < (d/16)*B^2) :
    Tendsto (fun n : ℕ => (n : ℝ)^m*gaussianTruncationTail μ d
      (B*Real.sqrt (Real.log (n : ℝ)))) atTop (𝓝 0) := by
  have hh := (polynomial_logarithmic_cutoff_tendsto m (d/16) B h).mul_const
    ((16/d)*gaussianErrorExpBound μ d)
  convert! hh using 1
  · funext n
    unfold gaussianTruncationTail
    ring
  · ring

/-- The full n(n+1) bad-prefix envelope vanishes at a logarithmic cutoff. -/
theorem matrixBadPrefix_logarithmic_bound_tendsto (c A M : ℝ)
    (h : 2 < (c/2)*A^2) :
    Tendsto (fun n : ℕ => (n : ℝ)*((n+1 : ℕ)*(M*
      Real.exp (-(c/2)*(A*Real.sqrt (Real.log (n : ℝ)))^2)))) atTop (𝓝 0) := by
  have h2 := polynomial_logarithmic_cutoff_tendsto 2 (c/2) A h
  have h1 := polynomial_logarithmic_cutoff_tendsto 1 (c/2) A (by norm_num; linarith)
  have hh := (h2.add h1).mul_const M
  convert! hh using 1
  · funext n
    push_cast
    ring
  · ring

#print axioms gaussianLogarithmicCutoff_smallness
#print axioms gaussianTruncationTail_logarithmic_tendsto
#print axioms matrixBadPrefix_logarithmic_bound_tendsto
end SpectralRadiusUpperTail
