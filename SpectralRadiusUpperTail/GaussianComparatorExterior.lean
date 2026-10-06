import SpectralRadiusUpperTail.GaussianComparatorEntries
import SpectralRadiusUpperTail.IidExteriorResolvent

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma gaussianComparator_exterior_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℂ) (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ =>
      (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
        {x | ¬ matrixExteriorControl (normalizedArray (fun i => comparatorVector n (x i))) r C})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hlim⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  refine ⟨C,hC,squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim⟩
  intro n
  exact gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
    (fun A => ¬ matrixExteriorControl A r C)

#print axioms gaussianComparator_exterior_probability
end SpectralRadiusUpperTail
