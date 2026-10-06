import SpectralRadiusUpperTail.CouplingKernel
import SpectralRadiusUpperTail.FiniteSequentialLaw

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

/-- Iterate the explicit common-part density couplings on the full paired history. -/
noncomputable def densitySequentialLaw (μ : Measure α) [SFinite μ]
    (k : (n : ℕ) → (Fin n → α × α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n))) (n : ℕ) :
    Measure (Fin n → α × α) :=
  finiteCoupledLaw (fun j => densityCouplingKernel μ (k j) (hk j)) n

theorem densitySequentialLaw_probability (μ : Measure α) [IsProbabilityMeasure μ]
    (k : (n : ℕ) → (Fin n → α × α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n)))
    (hnorm : ∀ n s, (∫⁻ x, k n s x ∂μ) = 1) (n : ℕ) :
    IsProbabilityMeasure (densitySequentialLaw μ k hk n) := by
  let κ := fun j => densityCouplingKernel μ (k j) (hk j)
  have : ∀ j, IsMarkovKernel (κ j) := fun j =>
    densityCouplingKernel_markov μ (k j) (hk j) (hnorm j)
  exact finiteCoupledLaw_probability κ n

/-- The actual finite array constructed from normalized measurable density
couplings has an iid comparator, with the exact original product measure. -/
theorem densitySequentialLaw_comparator_iid (μ : Measure α) [IsProbabilityMeasure μ]
    (k : (n : ℕ) → (Fin n → α × α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n)))
    (hnorm : ∀ n s, (∫⁻ x, k n s x ∂μ) = 1) (n : ℕ) :
    (densitySequentialLaw μ k hk n).map (comparatorVector n) =
      Measure.pi (fun _ : Fin n => μ) := by
  let κ := fun j => densityCouplingKernel μ (k j) (hk j)
  have : ∀ j, IsMarkovKernel (κ j) := fun j =>
    densityCouplingKernel_markov μ (k j) (hk j) (hnorm j)
  exact finiteCoupledLaw_comparator_iid μ κ
    (fun j s => (densityCouplingKernel_marginals μ (k j) (hk j) (hnorm j) s).2) n

#print axioms densitySequentialLaw_comparator_iid
end SpectralRadiusUpperTail
