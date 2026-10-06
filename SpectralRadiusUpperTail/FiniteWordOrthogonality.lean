import SpectralRadiusUpperTail.IidSimpleWordVariance

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma finite_word_pair_integrable {σ ι κ τ υ : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    (c : ι → ℝ) (d : κ → ℝ) (e : ι → τ → σ) (f : κ → υ → σ) :
    Integrable (fun x : σ → ℝ => (∑ i, c i * ∏ a, x (e i a)) *
      (∑ j, d j * ∏ b, x (f j b))) (Measure.pi (fun _ => μ)) := by
  classical
  simp_rw [Finset.sum_mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (iid_real_word_pair_integrable μ hi (e i) (f j)).const_mul (c i*d j)
  exact h.congr (Filter.Eventually.of_forall (fun x => by ring))

/-- Finite linear combinations preserve cross orthogonality of words.
Their coordinates can overlap; independence is only used in the word estimates. -/
theorem finite_word_cross_zero {σ ι κ τ υ : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ)
    (c : ι → ℝ) (d : κ → ℝ) (e : ι → τ → σ) (f : κ → υ → σ)
    (hz : ∀ i j, (∫ x : σ → ℝ, (∏ a, x (e i a)) * (∏ b, x (f j b))
      ∂Measure.pi (fun _ => μ)) = 0) :
    Integrable (fun x : σ → ℝ => (∑ i, c i * ∏ a, x (e i a)) *
      (∑ j, d j * ∏ b, x (f j b))) (Measure.pi (fun _ => μ)) ∧
    (∫ x : σ → ℝ, (∑ i, c i * ∏ a, x (e i a)) *
      (∑ j, d j * ∏ b, x (f j b)) ∂Measure.pi (fun _ => μ)) = 0 := by
  classical
  have heq (x : σ → ℝ) : (∑ i, c i * ∏ a, x (e i a)) *
      (∑ j, d j * ∏ b, x (f j b)) =
      ∑ i, ∑ j, (c i*d j) * ((∏ a, x (e i a))*(∏ b, x (f j b))) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have ht (i : ι) (j : κ) :=
    (iid_real_word_pair_integrable μ hi (e i) (f j)).const_mul (c i*d j)
  simp_rw [heq]
  constructor
  · exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))
  · rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ht i j))]
    simp_rw [integral_finsetSum _ (fun j _ => ht _ j), integral_const_mul, hz]
    simp

#print axioms finite_word_cross_zero
end SpectralRadiusUpperTail
