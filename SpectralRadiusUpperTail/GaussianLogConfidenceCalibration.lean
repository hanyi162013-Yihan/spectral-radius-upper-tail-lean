import SpectralRadiusUpperTail.GaussianLogConfidence
import SpectralRadiusUpperTail.AffineConfidenceCalibration
import SpectralRadiusUpperTail.LogQuarterRate

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Calibration of the actual confidence threshold at the quarter-power rate. -/
theorem gaussianLogConfidenceThreshold_calibration (μ : Measure 𝕂)
    (a d A B L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      gaussianLogConfidenceThreshold μ a d A B L n ≤ C*logQuarterRate n := by
  let c := 12*gaussianScoreConstant a
    (rowSquareExpExponent (4*d) (∫ x : 𝕂, Real.exp (4*d*‖x‖^2) ∂μ))
    (Real.log 2)*gaussianLocalMomentCost μ d/d
  refine ⟨4*Real.sqrt (2*(|c| *(A+2)*L))+32*(B+1), by positivity, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ),
    logQuarterRate_tendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hl hn hr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have hx : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hl
  have hh := affine_confidence_calibration c A B L
    (Real.sqrt (Real.log (n : ℝ))) (Real.sqrt (n : ℝ)) (logQuarterRate n)
    hA hB hL hx (Real.sqrt_pos.mpr hn0) (logQuarterRate_nonneg n hn) hr.le
    (logQuarterRate_square n hn)
  rw [Real.sq_sqrt (by linarith : 0 ≤ Real.log (n : ℝ))] at hh
  convert hh using 1 <;> unfold gaussianLogConfidenceThreshold gaussianTruncationScale c <;> ring

#print axioms gaussianLogConfidenceThreshold_calibration
end SpectralRadiusUpperTail
