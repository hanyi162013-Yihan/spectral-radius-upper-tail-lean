import SpectralRadiusUpperTail.IidIsotropicResolvent

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

/-- A fixed finite family of deterministic directions is controlled simultaneously. -/
lemma iid_finite_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    {ι : Type*} [Fintype ι]
    (p q : ι → (n : ℕ) → Fin n → ℂ)
    (hp : ∀ a n, (∑ i, ‖p a n i‖^2) ≤ 1)
    (hq : ∀ a n, (∑ i, ‖q a n i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ∃ a, ¬ matrixIsotropicControl (normalizedIidMatrix x) (p a n) (q a n) r ε})
      atTop (𝓝 0) := by
  classical
  have hh := finite_union_probability_tendsto (Finset.univ : Finset ι)
    (fun n => Fin n × Fin n → ℂ) (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun a n => {x | ¬ matrixIsotropicControl (normalizedIidMatrix x) (p a n) (q a n) r ε})
    (fun a _ => iid_isotropic_resolvent_probability μ c hc hexp hm hv
      (p a) (q a) (hp a) (hq a) r ε hr hε)
  simpa only [Finset.mem_univ,Set.iUnion_true,Set.mem_setOf_eq,Set.mem_iUnion,
    Set.setOf_exists] using hh

#print axioms iid_finite_isotropic_probability
end SpectralRadiusUpperTail
