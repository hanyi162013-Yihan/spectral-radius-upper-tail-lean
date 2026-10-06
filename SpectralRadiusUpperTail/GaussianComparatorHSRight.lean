import SpectralRadiusUpperTail.IidHSRightDeformation
import SpectralRadiusUpperTail.GaussianComparatorEntries

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma gaussianComparator_HS_right_annulus_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℂ)
    (D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (C : ℝ) (hC : 0 < C)
    (hD : ∀ n, matrixHSsq (D n) ≤ C^2)
    (r L : ℝ) (hr : 1 < r) (hL : 0 < L) :
    ∃ B : ℝ, 0 < B ∧ Tendsto (fun n : ℕ =>
      (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
        {x | ¬ matrixAnnulusControl ((normalizedArray (fun i => comparatorVector n (x i)))*(1+D n)) r L B})
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hlim⟩ := iid_HS_right_annulus_probability μ c hc hexp hm hv D C hC hD r L hr hL
  refine ⟨B,hB,squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim⟩
  intro n
  exact gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
    (fun A => ¬ matrixAnnulusControl (A*(1+D n)) r L B)

#print axioms gaussianComparator_HS_right_annulus_probability
end SpectralRadiusUpperTail
