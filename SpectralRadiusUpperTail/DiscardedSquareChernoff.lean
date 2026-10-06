import SpectralRadiusUpperTail.DiscardedSquareMGF
import SpectralRadiusUpperTail.IidExponentialSumTail

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma discardedSquare_fixed_cutoff_tail (μ : Measure E) [IsProbabilityMeasure μ]
    (c a : ℝ) (hc : 0 < c) (ha : 0 < a)
    (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    ∃ K : ℕ, ∀ N : ℕ,
      (Measure.pi (fun _ : Fin N => μ)).real
        {x | (N : ℝ)*a ≤ ∑ i, discardedSquare (K : ℝ) (x i)} ≤
          Real.exp (-c*a*(N : ℝ)/2) := by
  have he := (tendsto_order.1 (discardedSquare_log_mgf_tendsto_zero μ c hi)).2
    (c*a/2) (by positivity)
  obtain ⟨K,hK⟩ := he.exists
  refine ⟨K,fun N => ?_⟩
  exact iid_exponential_sum_tail μ (discardedSquare (K : ℝ)) c a hc
    (discardedSquare_exp_integrable μ c (K : ℝ) hc.le hi) hK.le N

/-- The cutoff is fixed before the matrix dimension, and the error has quadratic speed. -/
lemma discardedSquare_quadratic_tail (μ : Measure E) [IsProbabilityMeasure μ]
    (c a : ℝ) (hc : 0 < c) (ha : 0 < a)
    (hi : Integrable (fun x : E => Real.exp (c*‖x‖^2)) μ) :
    ∃ K : ℕ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin (n*n) => μ)).real
        {x | (n : ℝ)^2*a ≤ ∑ i, discardedSquare (K : ℝ) (x i)} ≤
          Real.exp (-c*a*(n : ℝ)^2/2) := by
  obtain ⟨K,hK⟩ := discardedSquare_fixed_cutoff_tail μ c a hc ha hi
  refine ⟨K,fun n => ?_⟩
  simpa only [Nat.cast_mul,pow_two] using hK (n*n)

#print axioms discardedSquare_fixed_cutoff_tail
#print axioms discardedSquare_quadratic_tail
end SpectralRadiusUpperTail
