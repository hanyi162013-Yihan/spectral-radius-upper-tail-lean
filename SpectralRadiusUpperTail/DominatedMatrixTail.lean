import SpectralRadiusUpperTail.SpectralTail

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {n : ℕ}

lemma product_scaledFrobeniusPowerSquared_integrable
    (μ : (Fin n × Fin n) → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hint : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (c : ℝ) (k : ℕ) :
    Integrable (scaledFrobeniusPowerSquared c k) (Measure.pi μ) := by
  exact ((frobeniusPowerSquared_integrable μ hint k).const_mul ((c^k)^2)).congr
    (Filter.Eventually.of_forall (fun x => (scaledFrobeniusPowerSquared_eq c k x).symm))

theorem scaled_matrix_power_moment_comparison
    (μ ν : (Fin n × Fin n) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hintμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i))
    (hintν : ∀ i k, Integrable (fun x : ℝ => x^k) (ν i))
    (hpos : ∀ i k, 0 ≤ ∫ x : ℝ, x^k ∂μ i)
    (hdom : ∀ i k, (∫ x : ℝ, x^k ∂μ i) ≤ ∫ x : ℝ, x^k ∂ν i)
    (c : ℝ) (k : ℕ) :
    (∫ x, scaledFrobeniusPowerSquared c k x ∂Measure.pi μ) ≤
      ∫ x, scaledFrobeniusPowerSquared c k x ∂Measure.pi ν := by
  simp_rw [scaledFrobeniusPowerSquared_eq, integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (matrix_power_moment_comparison μ ν hintμ hintν hpos hdom k) (sq_nonneg _)

/-- Finite spectral-tail comparison for independent entry laws with dominated moments.
Only scalar entry moments are hypotheses; the spectral event bound is the conclusion. -/
theorem dominated_matrix_spectral_tail_le_moment
    (μ ν : (Fin n × Fin n) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, SigmaFinite (ν i)]
    (hintμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i))
    (hintν : ∀ i k, Integrable (fun x : ℝ => x^k) (ν i))
    (hpos : ∀ i k, 0 ≤ ∫ x : ℝ, x^k ∂μ i)
    (hdom : ∀ i k, (∫ x : ℝ, x^k ∂μ i) ≤ ∫ x : ℝ, x^k ∂ν i)
    (c r : ℝ) (hr : 0 < r) (k : ℕ) (hk : k ≠ 0) :
    (Measure.pi μ).real {x | r ≤ realMatrixRadius (c • entryMatrix x)} ≤
      (∫ x, scaledFrobeniusPowerSquared c k x ∂Measure.pi ν) / r^(2*k) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (scaledFrobeniusPowerSquared_nonneg c k))
    (product_scaledFrobeniusPowerSquared_integrable μ hintμ c k) (r^(2*k))
  have hprob := measureReal_mono (μ := Measure.pi μ)
    (spectral_tail_subset_power_event (n := n) c r hr.le k hk)
  have hbound : r^(2*k) * (Measure.pi μ).real
      {x | r ≤ realMatrixRadius (c • entryMatrix x)} ≤
      ∫ x, scaledFrobeniusPowerSquared c k x ∂Measure.pi ν :=
    (mul_le_mul_of_nonneg_left hprob (pow_nonneg hr.le _)).trans
      (hm.trans (scaled_matrix_power_moment_comparison μ ν hintμ hintν hpos hdom c k))
  exact (le_div_iff₀ (pow_pos hr _)).2 (by simpa only [mul_comm] using hbound)

#print axioms dominated_matrix_spectral_tail_le_moment
end SpectralRadiusUpperTail
