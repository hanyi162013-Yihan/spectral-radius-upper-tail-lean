import SpectralRadiusUpperTail.TiltEventPositive
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma log_bounds_of_exponential_bounds (p L ε : ℝ) (n : ℕ) (hn : 0 < n)
    (hl : Real.exp ((n : ℝ)*(L-ε)) ≤ p)
    (hu : p ≤ Real.exp ((n : ℝ)*(L+ε))) :
    L-ε ≤ Real.log p/(n : ℝ) ∧ Real.log p/(n : ℝ) ≤ L+ε := by
  have hp : 0 < p := (Real.exp_pos _).trans_le hl
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hll := Real.log_le_log (Real.exp_pos _) hl
  have hlu := Real.log_le_log hp hu
  rw [Real.log_exp] at hll hlu
  constructor
  · exact (le_div_iff₀ hnR).mpr (by simpa only [mul_comm] using hll)
  · exact (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hlu)

/-- Two-sided exponential bounds imply the normalized logarithmic limit,
including eventual positivity of the probabilities. -/
lemma tendsto_log_of_exponential_bounds (p : ℕ → ℝ) (L : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(L-ε)) ≤ p n ∧ p n ≤ Real.exp ((n : ℝ)*(L+ε))) :
    Tendsto (fun n => Real.log (p n)/(n : ℝ)) atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h (ε/2) (by positivity), eventually_gt_atTop 0] with n hn hn0
  obtain ⟨hl, hu⟩ := log_bounds_of_exponential_bounds (p n) L (ε/2) n hn0 hn.1 hn.2
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

#print axioms log_bounds_of_exponential_bounds
#print axioms tendsto_log_of_exponential_bounds
end SpectralRadiusUpperTail
