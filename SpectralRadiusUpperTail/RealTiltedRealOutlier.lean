import SpectralRadiusUpperTail.RealTiltedCenteredIsotropic
import SpectralRadiusUpperTail.RealOutlierProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma real_tilted_real_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 0 ≤ L)
    (v : ℕ → ℕ → ℝ) (hv : ∀ n, (∑ j : Fin n, ‖v n j.val‖^2) ≤ 1)
    (hunit : ∀ n, 0 < n → (∑ j : Fin n, ‖v n j.val‖^2) = 1)
    (hflat : ∀ n, ∀ j : Fin n, ‖v n j.val‖ ≤ L/Real.sqrt (n : ℝ))
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖(b : ℂ)‖-1) :
    Tendsto (fun n => (gaussianSequentialMatrixLaw μ (v n) (2*η) (rankOneTiltTarget η b (v n))).real
      {x | ¬ ∃ z : ℝ, (z : ℂ) ∈ closedBall (b : ℂ) d ∧ (z : ℂ) ∈ spectrum ℂ
        ((normalizedArray (fun i => coordinateVector Prod.fst n (x i))).map Complex.ofRealHom)}) atTop (𝓝 0) := by
  have (n : ℕ) : IsProbabilityMeasure (gaussianSequentialMatrixLaw μ (v n) (2*η) (rankOneTiltTarget (n := n) η b (v n))) :=
    gaussianSequentialMatrixLaw_probability μ (v n) (2*η) (by positivity) _
  have ht := real_outlier_probability_of_annulus_isotropic
    (fun n => Fin n → Fin n → ℝ × ℝ)
    (fun n => gaussianSequentialMatrixLaw μ (v n) (2*η) (rankOneTiltTarget η b (v n)))
    (fun n x => normalizedArray (fun i => coordinateVector Prod.fst n (x i))-
      b • Matrix.vecMulVec (fun i : Fin n => v n i.val) (fun i : Fin n => v n i.val))
    (fun n i => v n i.val) hunit b d hd hgap
    (fun r R ε hr hR hε => real_tilted_centered_isotropic_probability μ hm hvar c hc hexp
      η L hη hL v hv hunit hflat b r R ε hr hR hε)
  simpa only [Matrix.map_sub _ (map_sub _),real_rankOne_map,sub_add_cancel] using ht

#print axioms real_tilted_real_outlier_probability
end SpectralRadiusUpperTail
