import SpectralRadiusUpperTail.ComplexTiltedOutlier
import SpectralRadiusUpperTail.RealTiltedOutlier
import SpectralRadiusUpperTail.OutlierEventMeasurable
import SpectralRadiusUpperTail.GaussianSourceEvents

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma complex_gaussianTilted_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℂ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ η (v n) (rankOneTiltTarget (n := n) η b (v n))).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ
        (normalizedArray x)}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2)
  have ht := complex_tilted_outlier_probability μ hm hvar hpseudo c hc hexp
    η L hη hL v hv hunit hflat b d hd hgap
  convert ht using 1
  funext n
  apply gaussian_source_event_probability_eq μ hX hm hvar (v n) (hv n) η (by positivity)
    (rankOneTiltTarget (n := n) η b (v n))
    (fun A => ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ A)
  exact (measurableSet_matrix_outlier_event n b d).compl

lemma real_gaussianTilted_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖(b : ℂ)‖-1) :
    Tendsto (fun n => (gaussianTiltedMatrixLaw μ (2*η) (v n) (rankOneTiltTarget (n := n) η b (v n))).real
      {x | ¬ ∃ z ∈ closedBall (b : ℂ) d, z ∈ spectrum ℂ
        ((normalizedArray x).map Complex.ofRealHom)}) atTop (𝓝 0) := by
  have hX : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
      (squareExp_norm_pow_integrable μ (4*c) (by positivity) hexp 2)
  have ht := real_tilted_outlier_probability μ hm hvar c hc hexp
    η L hη hL v hv hunit hflat b d hd hgap
  convert ht using 1
  funext n
  apply gaussian_source_event_probability_eq μ hX hm hvar (v n) (hv n) (2*η) (by positivity)
    (rankOneTiltTarget (n := n) η b (v n))
    (fun A => ¬ ∃ z ∈ closedBall (b : ℂ) d, z ∈ spectrum ℂ (A.map Complex.ofRealHom))
  exact ((measurableSet_matrix_outlier_event n (b : ℂ) d).compl).preimage
    (show Measurable (fun A : Matrix (Fin n) (Fin n) ℝ => A.map Complex.ofRealHom) from
      (continuous_id.matrix_map Complex.continuous_ofReal).measurable)

#print axioms complex_gaussianTilted_outlier_probability
#print axioms real_gaussianTilted_outlier_probability
end SpectralRadiusUpperTail
