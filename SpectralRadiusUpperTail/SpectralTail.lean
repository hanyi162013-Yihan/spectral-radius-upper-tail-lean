import SpectralRadiusUpperTail.SpectralWitness
import Mathlib.MeasureTheory.Measure.Real

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {n : ℕ}

lemma scaledFrobeniusPowerSquared_nonneg (c : ℝ) (k : ℕ)
    (x : (Fin n × Fin n) → ℝ) : 0 ≤ scaledFrobeniusPowerSquared c k x := by
  rw [scaledFrobeniusPowerSquared_eq]
  exact mul_nonneg (sq_nonneg _) (frobeniusPowerSquared_nonneg k x)

lemma sign_scaledFrobeniusPowerSquared_integrable (c : ℝ) (n k : ℕ) :
    Integrable (scaledFrobeniusPowerSquared c k) (signMatrixLaw n) := by
  have h := (frobeniusPowerSquared_integrable (n := n) (fun _ => signMeasure)
    (fun _ _ => sign_integrable _) k).const_mul ((c^k)^2)
  exact h.congr (Filter.Eventually.of_forall
    (fun x => (scaledFrobeniusPowerSquared_eq c k x).symm))

/-- A spectral-radius event forces a large nonnegative matrix-power polynomial. -/
theorem spectral_tail_subset_power_event (c r : ℝ) (hr : 0 ≤ r)
    (k : ℕ) (hk : k ≠ 0) :
    {x : (Fin n × Fin n) → ℝ | r ≤ realMatrixRadius (c • entryMatrix x)} ⊆
      {x | r^(2*k) ≤ scaledFrobeniusPowerSquared c k x} := by
  intro x hx
  have hp : r^k ≤ realMatrixRadius (c • entryMatrix x)^k := by
    exact pow_le_pow_left₀ hr hx k
  have hs := mul_self_le_mul_self (pow_nonneg hr k) hp
  calc
    r^(2*k) = (r^k)^2 := by rw [Nat.mul_comm 2 k, pow_mul]
    _ ≤ (realMatrixRadius (c • entryMatrix x)^k)^2 := by simpa only [sq] using hs
    _ ≤ scaledFrobeniusPowerSquared c k x :=
      realMatrixRadius_power_sq_le _ k hk

/-- Finite-dimensional upper tail of an actual iid normalized Bernoulli matrix.
The right-hand side is the actual Gaussian matrix-power integral. -/
theorem sign_matrix_spectral_tail_le_gaussian_moment (n k : ℕ) (hk : k ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    (signMatrixLaw n).real
        {x | r ≤ realMatrixRadius ((1 / Real.sqrt n) • entryMatrix x)} ≤
      (∫ x, scaledFrobeniusPowerSquared (1 / Real.sqrt n) k x ∂gaussianMatrixLaw n) /
        r^(2*k) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (scaledFrobeniusPowerSquared_nonneg (1 / Real.sqrt n) k))
    (sign_scaledFrobeniusPowerSquared_integrable (1 / Real.sqrt n) n k) (r^(2*k))
  have hsub := spectral_tail_subset_power_event (n := n) (1 / Real.sqrt n) r hr.le k hk
  have hprob := measureReal_mono (μ := signMatrixLaw n) hsub
  have hbound : r^(2*k) * (signMatrixLaw n).real
      {x | r ≤ realMatrixRadius ((1 / Real.sqrt n) • entryMatrix x)} ≤
      ∫ x, scaledFrobeniusPowerSquared (1 / Real.sqrt n) k x ∂gaussianMatrixLaw n :=
    (mul_le_mul_of_nonneg_left hprob (pow_nonneg hr.le _)).trans
      (hm.trans (normalized_sign_matrix_power_moment_le_gaussian n k))
  exact (le_div_iff₀ (pow_pos hr _)).2 (by simpa only [mul_comm] using hbound)

#print axioms spectral_tail_subset_power_event
#print axioms sign_matrix_spectral_tail_le_gaussian_moment
end SpectralRadiusUpperTail
