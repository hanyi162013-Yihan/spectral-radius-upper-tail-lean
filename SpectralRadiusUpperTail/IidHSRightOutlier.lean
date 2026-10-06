import SpectralRadiusUpperTail.OutlierProbability
import SpectralRadiusUpperTail.HSRightIsotropicTransfers

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma iid_HS_right_outlier_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (v : (n : ℕ) → Fin n → ℂ)
    (hunit : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1)
    (henergy : ∀ n, (∑ i, ‖v n i‖^2) ≤ 1)
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ
        (normalizedIidMatrix x*(1+D n)+b • Matrix.vecMulVec (v n) (star (v n)))})
      atTop (𝓝 0) := by
  apply outlier_probability_of_annulus_isotropic
    (fun n => Fin n × Fin n → ℂ) (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun n x => normalizedIidMatrix x*(1+D n)) v hunit b d hd hgap
  intro r L ε hr hL hε
  exact iid_HS_right_isotropic_probability μ c hc hexp hm hv D C hC hD
    v v henergy henergy r L ε hr hL hε

lemma iid_real_HS_right_outlier_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (v : (n : ℕ) → Fin n → ℂ)
    (hunit : ∀ n, 0 < n → (∑ i, ‖v n i‖^2) = 1)
    (henergy : ∀ n, (∑ i, ‖v n i‖^2) ≤ 1)
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ
        (((normalizedIidMatrix x).map Complex.ofRealHom)*(1+D n)+
          b • Matrix.vecMulVec (v n) (star (v n)))}) atTop (𝓝 0) := by
  apply outlier_probability_of_annulus_isotropic
    (fun n => Fin n × Fin n → ℝ) (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun n x => ((normalizedIidMatrix x).map Complex.ofRealHom)*(1+D n))
    v hunit b d hd hgap
  intro r L ε hr hL hε
  exact iid_real_HS_right_isotropic_probability μ c hc hexp hm hv D C hC hD
    v v henergy henergy r L ε hr hL hε

#print axioms iid_HS_right_outlier_probability
#print axioms iid_real_HS_right_outlier_probability
end SpectralRadiusUpperTail
