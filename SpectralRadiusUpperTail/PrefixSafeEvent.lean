import SpectralRadiusUpperTail.PredictableIndicator

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]

/-- All targets seen through the current time remain inside the cutoff. -/
def prefixSafeEvent (Y : ℕ → Ω → E) (R : ℝ) (n : ℕ) : Set Ω :=
  {x | ∀ k ≤ n, ‖Y k x‖ ≤ R}

lemma prefixSafeEvent_antitone (Y : ℕ → Ω → E) (R : ℝ) :
    Antitone (prefixSafeEvent Y R) := by
  intro i j hij x hx k hk
  exact hx k (hk.trans hij)

/-- The cutoff decision is measurable before the next increment is revealed. -/
lemma prefixSafeEvent_measurable (F : Filtration ℕ mΩ) (Y : ℕ → Ω → E)
    (hY : ∀ n, Measurable[F n] (Y n)) (R : ℝ) (n : ℕ) :
    MeasurableSet[F n] (prefixSafeEvent Y R n) := by
  letI : MeasurableSpace Ω := F n
  unfold prefixSafeEvent
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  exact measurableSet_le (((hY k).mono (F.mono hk) le_rfl).norm) measurable_const

lemma prefixSafeEvent_mem_current (Y : ℕ → Ω → E) (R : ℝ) (n : ℕ)
    {x : Ω} (hx : x ∈ prefixSafeEvent Y R n) : ‖Y n x‖ ≤ R := hx n le_rfl

/-- Before any bad prefix, stopping leaves every preceding increment intact. -/
lemma prefixSafeEvent_indicator_eq (Y : ℕ → Ω → E) (R : ℝ)
    {V : Type*} [Zero V] (d : ℕ → Ω → V) (n k : ℕ) (hk : k ≤ n)
    {x : Ω} (hx : x ∈ prefixSafeEvent Y R n) :
    (prefixSafeEvent Y R k).indicator (d k) x = d k x :=
  Set.indicator_of_mem (prefixSafeEvent_antitone Y R hk hx) _

#print axioms prefixSafeEvent_measurable
end SpectralRadiusUpperTail
