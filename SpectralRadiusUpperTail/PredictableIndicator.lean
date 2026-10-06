import SpectralRadiusUpperTail.IncrementMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A decision measurable before an increment is revealed preserves its
actual integrability and conditional-zero property. -/
theorem predictableIndicator_condExp_zero (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (d : ℕ → Ω → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet[F n] (A n)) (hi : ∀ n, Integrable (d n) P)
    (hz : ∀ n, P[d n | F n] =ᵐ[P] 0) (n : ℕ) :
    Integrable ((A n).indicator (d n)) P ∧
      P[(A n).indicator (d n) | F n] =ᵐ[P] 0 := by
  refine ⟨(hi n).indicator ((F.le n) _ (hA n)), ?_⟩
  apply (condExp_indicator (hi n) (hA n)).trans
  filter_upwards [hz n] with x hx
  by_cases h : x ∈ A n
  · simpa only [Set.indicator_of_mem h, Pi.zero_apply] using hx
  · simp only [Set.indicator_of_notMem h, Pi.zero_apply]

/-- The stopped sum is an actual martingale when each decision uses only the
preceding filtration. No stopping or independence property is inferred from marginals. -/
theorem martingale_predictableIndicator (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (d : ℕ → Ω → E) (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet[F n] (A n))
    (hd : ∀ n, StronglyMeasurable[F (n+1)] (d n))
    (hi : ∀ n, Integrable (d n) P) (hz : ∀ n, P[d n | F n] =ᵐ[P] 0) :
    Martingale (incrementPartialSum (fun n => (A n).indicator (d n))) F P := by
  apply martingale_incrementPartialSum
  · intro n
    exact (hd n).indicator ((F.mono (Nat.le_succ n)) _ (hA n))
  · intro n
    exact (predictableIndicator_condExp_zero P F d A hA hi hz n).1
  · intro n
    exact (predictableIndicator_condExp_zero P F d A hA hi hz n).2

#print axioms martingale_predictableIndicator
end SpectralRadiusUpperTail
