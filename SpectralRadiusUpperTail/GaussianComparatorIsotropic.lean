import SpectralRadiusUpperTail.GaussianComparatorEntries
import SpectralRadiusUpperTail.IidIsotropicResolvent

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

lemma gaussianComparator_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (v : ℕ → ℕ → ℂ) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (t : (n : ℕ) → Fin n → ℂ)
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (gaussianSequentialMatrixLaw μ (v n) (a n) (t n)).real
      {x | ¬ matrixIsotropicControl (normalizedArray (fun i => comparatorVector n (x i)))
        (p n) (q n) r ε}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (iid_isotropic_resolvent_probability μ c hc hexp hm hv p q hp hq r ε hr hε)
  intro n
  exact gaussianComparator_event_probability_le μ (v n) (a n) (ha n) (t n)
    (fun A => ¬ matrixIsotropicControl A (p n) (q n) r ε)

#print axioms gaussianComparator_isotropic_probability
end SpectralRadiusUpperTail
