import SpectralRadiusUpperTail.ConcreteDoobCoupling
import SpectralRadiusUpperTail.GaussianRevealedEntry
import SpectralRadiusUpperTail.GaussianRowRegressionMoment

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma gaussianRevealedWeight_measurable (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) :
    Measurable (revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t n) :=
  revealedWeight_measurable μ _ _ (fun _ => (continuous_const.mul continuous_id).measurable)
    (gaussianSoftWeight_measurable a) N t n

lemma gaussianRevealedWeight_ne_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) (s : Fin n → 𝕂) :
    revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t n s ≠ 0 :=
  ne_of_gt (futureWeight_pos μ _ _ (fun _ => (continuous_const.mul continuous_id).measurable)
    (gaussianSoftWeight_measurable a) (gaussianSoftWeight_pos a) _ _)

lemma gaussianRevealedWeight_ne_top (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) (s : Fin n → 𝕂) :
    revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t n s ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (futureWeight_le_one μ _ _ (gaussianSoftWeight_le_one a ha) _ _)

noncomputable def gaussianSequentialRowLaw (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) : Measure (Fin n → 𝕂 × 𝕂) :=
  doobCoupledPathLaw μ N (revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t)
    (gaussianRevealedWeight_measurable μ v a N t) n

noncomputable def gaussianSequentialKernel (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) :
    Kernel (Fin n → 𝕂 × 𝕂) (𝕂 × 𝕂) :=
  doobCoupledKernel μ N (revealedWeight μ (fun i x => v i*x) (gaussianSoftWeight a) N t)
    (gaussianRevealedWeight_measurable μ v a N t) n

lemma gaussianSequentialRowLaw_succ (μ : Measure 𝕂) [SFinite μ]
    (v : ℕ → 𝕂) (a : ℝ) (N : ℕ) (t : 𝕂) (n : ℕ) :
    gaussianSequentialRowLaw μ v a N t (n+1) =
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n).map
        (fun z => Fin.cons z.2 z.1) := rfl

lemma gaussianSequentialRowLaw_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) :
    IsProbabilityMeasure (gaussianSequentialRowLaw μ v a N t n) :=
  doobCoupledPathLaw_probability μ N _ _
    (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
    (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
    (revealedWeight_rec μ _ _ N t) n

lemma gaussianSequentialKernel_markov (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) :
    IsMarkovKernel (gaussianSequentialKernel μ v a N t n) :=
  doobCoupledKernel_markov μ N _ _
    (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
    (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
    (revealedWeight_rec μ _ _ N t) n

/-- Every actual transition retains the complete paired history, while its
source is the actual conditional entry law and its comparator has law mu. -/
theorem gaussianSequentialKernel_marginals (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) (s : Fin n → 𝕂 × 𝕂) :
    ((gaussianSequentialKernel μ v a N t n) s).map Prod.fst =
      gaussianEntryLaw μ a (fun i : Fin (N-(n+1)) => v i.val) (v (N-(n+1)))
        (t-revealedSum (fun i x => v i*x) N n (coordinateVector Prod.fst n s)) ∧
    ((gaussianSequentialKernel μ v a N t n) s).map Prod.snd = μ := by
  have hh := doobCoupledKernel_marginals μ N _ (gaussianRevealedWeight_measurable μ v a N t)
    (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
    (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
    (revealedWeight_rec μ _ _ N t) n s
  refine ⟨?_, hh.2⟩
  exact hh.1.trans (gaussianEntryLaw_eq_revealed_transition μ hX v N n hn a ha t
    (coordinateVector Prod.fst n s)).symm

lemma gaussianSequentialRowLaw_source (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (hm : (∫ x : 𝕂, x ∂μ) = 0)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1) (v : ℕ → 𝕂) (N : ℕ)
    (hv : ∑ j : Fin N, ‖v j.val‖^2 ≤ 1) (a : ℝ) (ha : 0 < a) (t : 𝕂) :
    (gaussianSequentialRowLaw μ v a N t N).map (coordinateVector Prod.fst N) =
      gaussianFiniteRowLaw μ a (fun j : Fin N => v j.val) t := by
  have hh := doobCoupledPathLaw_source μ N _ (gaussianRevealedWeight_measurable μ v a N t)
    (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
    (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
    (revealedWeight_rec μ _ _ N t) N le_rfl
  rw [gaussianFiniteRowLaw_eq_coupling_source μ hX hm hvar v N hv a ha]
  simp only [revealedWeight_zero, revealedWeight_terminal] at hh
  convert! hh using 1
  rw [gaussianRowNormalizer_eq_future μ v a ha]

lemma gaussianSequentialRowLaw_comparator (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a) (N : ℕ) (t : 𝕂) (n : ℕ) :
    (gaussianSequentialRowLaw μ v a N t n).map (comparatorVector n) =
      Measure.pi (fun _ : Fin n => μ) :=
  doobCoupledPathLaw_comparator μ N _ _
    (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
    (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
    (revealedWeight_rec μ _ _ N t) n

#print axioms gaussianSequentialKernel_marginals
#print axioms gaussianSequentialRowLaw_source
end SpectralRadiusUpperTail
