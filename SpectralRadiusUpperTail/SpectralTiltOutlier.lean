import SpectralRadiusUpperTail.GaussianTiltedOutlier
import SpectralRadiusUpperTail.SpectralTiltTarget

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma complex_spectralTilt_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖(b/((η^2+1 : ℝ) : ℂ))‖-1) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (η^2) (v n) (spectralTiltTarget (n := n) b (v n))).real
      {x | ¬ ∃ z ∈ closedBall (b/((η^2+1 : ℝ) : ℂ)) d, z ∈ spectrum ℂ
        (normalizedArray x)}) atTop (𝓝 0) := by
  have hη2 : 0 < η^2 := sq_pos_of_pos hη
  have ht := complex_gaussianTilted_outlier_probability μ hm hvar hpseudo c hc hexp
    (η^2) L hη2 hL v hv hunit hflat (b/((η^2+1 : ℝ) : ℂ)) d hd hgap
  convert ht using 1
  funext n
  exact congrArg (fun t : Fin n → ℂ =>
    (gaussianTiltedMatrixLaw μ (η^2) (v n) t).real
      {x | ¬ ∃ z ∈ closedBall (b/((η^2+1 : ℝ) : ℂ)) d,
        z ∈ spectrum ℂ (normalizedArray x)})
    (rankOneTiltTarget_reparametrize (n := n) (η^2) hη2 b (v n)).symm

lemma real_spectralTilt_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖((b/(η^2+1) : ℝ) : ℂ)‖-1) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (2*η^2) (v n) (spectralTiltTarget (n := n) b (v n))).real
      {x | ¬ ∃ z ∈ closedBall ((b/(η^2+1) : ℝ) : ℂ) d, z ∈ spectrum ℂ
        ((normalizedArray x).map Complex.ofRealHom)}) atTop (𝓝 0) := by
  have hη2 : 0 < η^2 := sq_pos_of_pos hη
  have ht := real_gaussianTilted_outlier_probability μ hm hvar c hc hexp
    (η^2) L hη2 hL v hv hunit hflat (b/((η^2+1 : ℝ) : ℝ)) d hd hgap
  convert ht using 1
  funext n
  exact congrArg (fun t : Fin n → ℝ =>
    (gaussianTiltedMatrixLaw μ (2*η^2) (v n) t).real
      {x | ¬ ∃ z ∈ closedBall ((b/(η^2+1) : ℝ) : ℂ) d,
        z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)})
    (rankOneTiltTarget_reparametrize (n := n) (η^2) hη2 b (v n)).symm

#print axioms complex_spectralTilt_outlier_probability
#print axioms real_spectralTilt_outlier_probability
end SpectralRadiusUpperTail
