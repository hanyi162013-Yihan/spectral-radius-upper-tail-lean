import SpectralRadiusUpperTail.IidHSRightDeformation
import SpectralRadiusUpperTail.RealIidMatrixEvents

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_real_HS_right_annulus_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (c*‖x‖^2)) μ)
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hv : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (r L : ℝ) (hr : 1 < r) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixAnnulusControl (((normalizedIidMatrix x).map Complex.ofRealHom)*(1+D n)) r L B})
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hlim⟩ := iid_HS_right_annulus_probability (complexifiedLaw μ) c hc
    (complexifiedLaw_squareExp μ c hexp)
    (by rw [complexifiedLaw_mean,hm]; rfl) (by rw [complexifiedLaw_energy,hv])
    D C hC hD r L hr hL
  refine ⟨B,hB,squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim⟩
  intro n
  exact real_iid_matrix_event_le_complex μ (fun A => ¬ matrixAnnulusControl (A*(1+D n)) r L B)

#print axioms iid_real_HS_right_annulus_probability
end SpectralRadiusUpperTail
