import SpectralRadiusUpperTail.IidIsotropicResolvent
import SpectralRadiusUpperTail.IsotropicProbabilityStability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

lemma iid_perturbed_isotropic_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (E : (n : ℕ) → (Fin n × Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (herr : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | δ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E n x)‖}) atTop (𝓝 0))
    (p q : (n : ℕ) → Fin n → ℂ)
    (hp : ∀ n, (∑ i, ‖p n i‖^2) ≤ 1) (hq : ∀ n, (∑ i, ‖q n i‖^2) ≤ 1)
    (r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ matrixIsotropicControl (normalizedIidMatrix x+E n x) (p n) (q n) r ε})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  exact isotropic_probability_stability (fun n => Fin n × Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun _ x => normalizedIidMatrix x) E p q hp hq r C hC hbase
    (fun δ hδ => iid_isotropic_resolvent_probability μ c hc hexp hm hv p q hp hq r δ hr hδ)
    herr ε hε

#print axioms iid_perturbed_isotropic_probability
end SpectralRadiusUpperTail
