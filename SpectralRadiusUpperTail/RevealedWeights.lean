import SpectralRadiusUpperTail.FutureWeight
import SpectralRadiusUpperTail.DoobDensity
import Mathlib.Algebra.BigOperators.Fin

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

variable {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
  [AddCommGroup E] [MeasurableAdd₂ E] [MeasurableSub₂ E]

/-- The history is prepended as coordinates are revealed in descending order. -/
def revealedSum (f : ℕ → α → E) (N n : ℕ) (s : Fin n → α) : E :=
  ∑ i : Fin n, f (N-n+i.val) (s i)

omit [MeasurableSub₂ E] in
lemma revealedSum_measurable (f : ℕ → α → E) (hf : ∀ n, Measurable (f n))
    (N n : ℕ) : Measurable (revealedSum f N n) := by
  exact Finset.measurable_sum Finset.univ
    (fun i _ => (hf (N-n+i.val)).comp (measurable_pi_apply i))

omit [MeasurableSpace α] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E] in
lemma revealedSum_cons (f : ℕ → α → E) (N n : ℕ) (hn : n < N)
    (s : Fin n → α) (x : α) :
    revealedSum f N (n+1) (Fin.cons x s) = f (N-(n+1)) x + revealedSum f N n s := by
  unfold revealedSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.add_zero, Fin.cons_zero, Fin.val_succ, Fin.cons_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : N-(n+1)+(i.val+1) = N-n+i.val := by omega
  rw [hi]

/-- Integrate over all coordinates not yet revealed. -/
noncomputable def revealedWeight (μ : Measure α) (f : ℕ → α → E) (w : E → ℝ≥0∞)
    (N : ℕ) (t : E) (n : ℕ) (s : Fin n → α) : ℝ≥0∞ :=
  futureWeight μ f w (N-n) (t-revealedSum f N n s)

lemma revealedWeight_measurable (μ : Measure α) [SFinite μ]
    (f : ℕ → α → E) (w : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hw : Measurable w)
    (N : ℕ) (t : E) (n : ℕ) : Measurable (revealedWeight μ f w N t n) :=
  (futureWeight_measurable μ f w hf hw (N-n)).comp
    (measurable_const.sub (revealedSum_measurable f hf N n))

lemma revealedWeight_rec (μ : Measure α) (f : ℕ → α → E) (w : E → ℝ≥0∞)
    (N : ℕ) (t : E) (n : ℕ) (hn : n < N) (s : Fin n → α) :
    (∫⁻ x, revealedWeight μ f w N t (n+1) (Fin.cons x s) ∂μ) =
      revealedWeight μ f w N t n s := by
  have hm : N-n = N-(n+1)+1 := by omega
  change (∫⁻ x, futureWeight μ f w (N-(n+1))
    (t-revealedSum f N (n+1) (Fin.cons x s)) ∂μ) =
      futureWeight μ f w (N-n) (t-revealedSum f N n s)
  rw [hm, futureWeight]
  apply lintegral_congr
  intro x
  rw [revealedSum_cons f N n hn, add_comm (f (N-(n+1)) x), sub_add_eq_sub_sub]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E] in
lemma revealedWeight_zero (μ : Measure α) (f : ℕ → α → E) (w : E → ℝ≥0∞)
    (N : ℕ) (t : E) (s : Fin 0 → α) :
    revealedWeight μ f w N t 0 s = futureWeight μ f w N t := by
  simp [revealedWeight, revealedSum]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSub₂ E] in
lemma revealedWeight_terminal (μ : Measure α) (f : ℕ → α → E) (w : E → ℝ≥0∞)
    (N : ℕ) (t : E) (s : Fin N → α) :
    revealedWeight μ f w N t N s = w (t-∑ i : Fin N, f i.val (s i)) := by
  simp [revealedWeight, revealedSum, futureWeight]

/-- Concrete sequential coupling for every bounded, strictly positive soft weight. -/
theorem softWeight_coupling_exists (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → E) (w : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hw : Measurable w)
    (hpos : ∀ s, 0 < w s) (hle : ∀ s, w s ≤ 1) (N : ℕ) (t : E) :
    ∃ Γ : Measure (Fin N → α × α), IsProbabilityMeasure Γ ∧
      Γ.map (coordinateVector Prod.fst N) =
        (Measure.pi (fun _ : Fin N => μ)).withDensity
          (fun s => w (t-∑ i : Fin N, f i.val (s i)) / futureWeight μ f w N t) ∧
      Γ.map (comparatorVector N) = Measure.pi (fun _ : Fin N => μ) := by
  have hzero : ∀ n ≤ N, ∀ s, revealedWeight μ f w N t n s ≠ 0 := by
    intro n _ s
    exact ne_of_gt (futureWeight_pos μ f w hf hw hpos _ _)
  have htop : ∀ n ≤ N, ∀ s, revealedWeight μ f w N t n s ≠ ∞ := by
    intro n _ s
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (futureWeight_le_one μ f w hle _ _)
  obtain ⟨Γ, hΓ, hfirst, hsecond⟩ := doob_coupling_exists μ N
    (revealedWeight μ f w N t) (revealedWeight_measurable μ f w hf hw N t)
    hzero htop (revealedWeight_rec μ f w N t)
  refine ⟨Γ, hΓ, ?_, hsecond⟩
  simpa only [revealedWeight_zero, revealedWeight_terminal] using hfirst

#print axioms revealedWeight_rec
#print axioms softWeight_coupling_exists
end SpectralRadiusUpperTail
