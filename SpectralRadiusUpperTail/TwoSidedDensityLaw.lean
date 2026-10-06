import SpectralRadiusUpperTail.DensitySequential
import SpectralRadiusUpperTail.FinitePathProjection

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Θ α : Type*} [MeasurableSpace Θ] [MeasurableSpace α]

noncomputable def densityKernel (μ : Measure α) [SFinite μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k)) : Kernel Θ α :=
  ⟨fun s => μ.withDensity (k s), measurable_parameter_withDensity μ k hk⟩

theorem densityKernel_markov (μ : Measure α) [IsProbabilityMeasure μ]
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k))
    (hnorm : ∀ s, (∫⁻ x, k s x ∂μ) = 1) : IsMarkovKernel (densityKernel μ k hk) :=
  ⟨fun s => normalizedDensity_probability μ (k s) (hnorm s)⟩

def liftHistoryDensity (n : ℕ) (k : (Fin n → α) → α → ℝ≥0∞)
    (s : Fin n → α × α) (x : α) : ℝ≥0∞ :=
  k (coordinateVector Prod.fst n s) x

lemma measurable_liftHistoryDensity (n : ℕ) (k : (Fin n → α) → α → ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) :
    Measurable (Function.uncurry (liftHistoryDensity n k)) :=
  hk.comp (((measurable_coordinateVector Prod.fst measurable_fst n).comp measurable_fst).prodMk
    measurable_snd)

noncomputable def densityPathLaw (μ : Measure α) [SFinite μ]
    (k : (n : ℕ) → (Fin n → α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n))) (n : ℕ) : Measure (Fin n → α) :=
  finitePathLaw (fun j => densityKernel μ (k j) (hk j)) n

noncomputable def pairedDensityPathLaw (μ : Measure α) [SFinite μ]
    (k : (n : ℕ) → (Fin n → α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n))) (n : ℕ) : Measure (Fin n → α × α) :=
  densitySequentialLaw μ (fun j => liftHistoryDensity j (k j))
    (fun j => measurable_liftHistoryDensity j (k j) (hk j)) n

theorem pairedDensityPathLaw_probability (μ : Measure α) [IsProbabilityMeasure μ]
    (k : (n : ℕ) → (Fin n → α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n)))
    (hnorm : ∀ n s, (∫⁻ x, k n s x ∂μ) = 1) (n : ℕ) :
    IsProbabilityMeasure (pairedDensityPathLaw μ k hk n) :=
  densitySequentialLaw_probability μ _ _
    (fun j s => hnorm j (coordinateVector Prod.fst j s)) n

/-- The source projection has exactly the prescribed density-transition law. -/
theorem pairedDensityPathLaw_source (μ : Measure α) [IsProbabilityMeasure μ]
    (k : (n : ℕ) → (Fin n → α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n)))
    (hnorm : ∀ n s, (∫⁻ x, k n s x ∂μ) = 1) (n : ℕ) :
    (pairedDensityPathLaw μ k hk n).map (coordinateVector Prod.fst n) =
      densityPathLaw μ k hk n := by
  let κ := fun j => densityCouplingKernel μ (liftHistoryDensity j (k j))
    (measurable_liftHistoryDensity j (k j) (hk j))
  let η := fun j => densityKernel μ (k j) (hk j)
  have : ∀ j, IsMarkovKernel (κ j) := fun j => densityCouplingKernel_markov μ _ _
    (fun s => hnorm j (coordinateVector Prod.fst j s))
  have : ∀ j, IsMarkovKernel (η j) := fun j => densityKernel_markov μ _ _ (hnorm j)
  apply finiteCoupledLaw_source_law κ η
  intro j s
  exact (densityCouplingKernel_marginals μ _ _
    (fun s => hnorm j (coordinateVector Prod.fst j s)) s).1

/-- Simultaneously, the comparator projection is the original iid product law. -/
theorem pairedDensityPathLaw_comparator (μ : Measure α) [IsProbabilityMeasure μ]
    (k : (n : ℕ) → (Fin n → α) → α → ℝ≥0∞)
    (hk : ∀ n, Measurable (Function.uncurry (k n)))
    (hnorm : ∀ n s, (∫⁻ x, k n s x ∂μ) = 1) (n : ℕ) :
    (pairedDensityPathLaw μ k hk n).map (comparatorVector n) =
      Measure.pi (fun _ : Fin n => μ) :=
  densitySequentialLaw_comparator_iid μ _ _
    (fun j s => hnorm j (coordinateVector Prod.fst j s)) n

#print axioms pairedDensityPathLaw_source
#print axioms pairedDensityPathLaw_comparator
end SpectralRadiusUpperTail
