import Mathlib.Probability.Martingale.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators MeasureTheory
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def incrementPartialSum (d : ℕ → Ω → E) (n : ℕ) (x : Ω) : E :=
  ∑ k ∈ Finset.range n, d k x

lemma incrementPartialSum_succ (d : ℕ → Ω → E) (n : ℕ) :
    incrementPartialSum d (n+1) = incrementPartialSum d n+d n := by
  funext x
  exact Finset.sum_range_succ (fun k => d k x) n

/-- Actual integrable martingale differences with next-step measurability
produce a martingale on the same probability space and filtration. -/
theorem martingale_incrementPartialSum (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (d : ℕ → Ω → E)
    (hd : ∀ n, StronglyMeasurable[F (n+1)] (d n))
    (hi : ∀ n, Integrable (d n) P)
    (hz : ∀ n, P[d n | F n] =ᵐ[P] 0) :
    Martingale (incrementPartialSum d) F P := by
  have had : StronglyAdapted F (incrementPartialSum d) := by
    intro n
    have hs (k : ℕ) (hk : k ∈ Finset.range n) : StronglyMeasurable[F n] (d k) :=
      (hd k).mono (F.mono (by have := Finset.mem_range.mp hk; omega))
    have he : incrementPartialSum d n = ∑ k ∈ Finset.range n, d k := by
      funext x
      simp only [incrementPartialSum, Finset.sum_apply]
    rw [he]
    exact Finset.stronglyMeasurable_sum (Finset.range n) hs
  have hint (n : ℕ) : Integrable (incrementPartialSum d n) P :=
    integrable_finsetSum _ (fun k _ => hi k)
  apply martingale_of_condExp_sub_eq_zero_nat had hint
  intro n
  rw [incrementPartialSum_succ, add_sub_cancel_left]
  exact hz n

#print axioms martingale_incrementPartialSum
end SpectralRadiusUpperTail
