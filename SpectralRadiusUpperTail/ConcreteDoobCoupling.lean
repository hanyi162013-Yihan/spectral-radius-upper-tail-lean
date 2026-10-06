import SpectralRadiusUpperTail.DoobDensity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

/-- A fixed sequential common-part coupling, retained at every intermediate
history length so that subsequent conditional arguments use its actual kernels. -/
noncomputable def doobCoupledPathLaw (μ : Measure α) [SFinite μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) : Measure (Fin n → α × α) :=
  pairedDensityPathLaw μ (doobDensity N A) (doobDensity_measurable N A hA) n

noncomputable def doobCoupledKernel (μ : Measure α) [SFinite μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) : Kernel (Fin n → α × α) (α × α) :=
  densityCouplingKernel μ (liftHistoryDensity n (doobDensity N A n))
    (measurable_liftHistoryDensity n _ (doobDensity_measurable N A hA n))

lemma doobCoupledPathLaw_succ (μ : Measure α) [SFinite μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) :
    doobCoupledPathLaw μ N A hA (n+1) =
      ((doobCoupledPathLaw μ N A hA n) ⊗ₘ doobCoupledKernel μ N A hA n).map
        (fun z => Fin.cons z.2 z.1) := rfl

section Normalized
variable (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n))
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s)

include hzero htop hrec

lemma doobCoupledPathLaw_probability (n : ℕ) :
    IsProbabilityMeasure (doobCoupledPathLaw μ N A hA n) :=
  pairedDensityPathLaw_probability μ _ _ (doobDensity_normalized μ N A hzero htop hrec) n

lemma doobCoupledKernel_markov (n : ℕ) : IsMarkovKernel (doobCoupledKernel μ N A hA n) :=
  densityCouplingKernel_markov μ _ _ (fun s =>
    doobDensity_normalized μ N A hzero htop hrec n (coordinateVector Prod.fst n s))

lemma doobCoupledKernel_marginals (n : ℕ) (s : Fin n → α × α) :
    ((doobCoupledKernel μ N A hA n) s).map Prod.fst =
      μ.withDensity (doobDensity N A n (coordinateVector Prod.fst n s)) ∧
    ((doobCoupledKernel μ N A hA n) s).map Prod.snd = μ :=
  densityCouplingKernel_marginals μ _ _ (fun s =>
    doobDensity_normalized μ N A hzero htop hrec n (coordinateVector Prod.fst n s)) s

lemma doobCoupledPathLaw_source (n : ℕ) (hn : n ≤ N) :
    (doobCoupledPathLaw μ N A hA n).map (coordinateVector Prod.fst n) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity
        (fun s => A n s / A 0 (fun i => Fin.elim0 i)) :=
  (pairedDensityPathLaw_source μ _ _ (doobDensity_normalized μ N A hzero htop hrec) n).trans
    (doobPathLaw_density μ N A hA hzero htop hrec n hn)

lemma doobCoupledPathLaw_comparator (n : ℕ) :
    (doobCoupledPathLaw μ N A hA n).map (comparatorVector n) =
      Measure.pi (fun _ : Fin n => μ) :=
  pairedDensityPathLaw_comparator μ _ _ (doobDensity_normalized μ N A hzero htop hrec) n

end Normalized
#print axioms doobCoupledKernel_marginals
#print axioms doobCoupledPathLaw_source
end SpectralRadiusUpperTail
