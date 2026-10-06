import SpectralRadiusUpperTail.RealUniformTiltedRealOutlier
import SpectralRadiusUpperTail.SpectralTiltTarget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix ENNReal

lemma real_spectralTilt_real_outlier_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (a L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖((b/(a+1) : ℝ) : ℂ)‖-1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ w : Fin n → ℝ, w ∈ flatUnitDirections ℝ n L →
      (gaussianTiltedMatrixLaw μ (2*a) (zeroExtendVector w)
        (spectralTiltTarget (n := n) b (zeroExtendVector w))).real
        {x | ¬ ∃ z : ℝ, (z : ℂ) ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d ∧
          (z : ℂ) ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)} < ε := by
  have hu := real_gaussianTilted_real_outlier_uniform μ hm hvar c hc hexp
    a L ha hL (b/(a+1)) d hd hgap ε hε
  filter_upwards [hu] with n hn w hw
  have he := congrArg (fun t : Fin n → ℝ =>
    (gaussianTiltedMatrixLaw μ (2*a) (zeroExtendVector w) t).real
      {x | ¬ ∃ z : ℝ, (z : ℂ) ∈ closedBall ((b/(a+1) : ℝ) : ℂ) d ∧
        (z : ℂ) ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)})
      (rankOneTiltTarget_reparametrize (n := n) a ha b (zeroExtendVector w))
  rw [← he]
  exact hn w hw


#print axioms real_spectralTilt_real_outlier_uniform
end SpectralRadiusUpperTail
