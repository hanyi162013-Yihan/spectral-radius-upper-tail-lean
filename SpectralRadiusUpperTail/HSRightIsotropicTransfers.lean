import SpectralRadiusUpperTail.IidHSRightIsotropic
import SpectralRadiusUpperTail.RealIidMatrixEvents
import SpectralRadiusUpperTail.GaussianComparatorEntries

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

lemma iid_real_HS_right_isotropic_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r L ε : ℝ) (hr : 1 < r) (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusIsotropicControl (((normalizedIidMatrix x).map Complex.ofRealHom)*(1+D n))
        (p n) (q n) r L ε}) atTop (𝓝 0) := by
  have ht := iid_HS_right_isotropic_probability (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean,hm]; rfl) (by rw [complexifiedLaw_energy,hv])
    D C hC hD p q hp hq r L ε hr hL hε
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => real_iid_matrix_event_le_complex μ
      (fun A => ¬ matrixAnnulusIsotropicControl (A*(1+D n)) (p n) (q n) r L ε)) ht

lemma gaussianComparator_HS_right_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℂ)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r L ε : ℝ) (hr : 1 < r) (hL : 0 < L) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ¬ matrixAnnulusIsotropicControl
        ((normalizedArray (fun i => comparatorVector n (x i)))*(1+D n)) (p n) (q n) r L ε})
      atTop (𝓝 0) := by
  have ht := iid_HS_right_isotropic_probability μ c hc hexp hm hv D C hC hD p q hp hq r L ε hr hL hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ ht
  intro n
  exact gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
    (fun A => ¬ matrixAnnulusIsotropicControl (A*(1+D n)) (p n) (q n) r L ε)

#print axioms iid_real_HS_right_isotropic_probability
#print axioms gaussianComparator_HS_right_isotropic_probability
end SpectralRadiusUpperTail
