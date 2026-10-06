import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma normalized_log_tendsto_of_error (Z e : ℕ → ℝ) (A : ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (h : ∀ n, 0 < n → |Real.log (Z n)-(n : ℝ)*A| ≤ (n : ℝ)*e n) :
    Tendsto (fun n => Real.log (Z n)/(n : ℝ)) atTop (𝓝 A) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_order.1 he).2 ε hε)
  refine ⟨max N 1,fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hid : Real.log (Z n)/(n : ℝ)-A = (Real.log (Z n)-(n : ℝ)*A)/(n : ℝ) := by
    field_simp
  rw [Real.dist_eq,hid,abs_div,abs_of_pos hnR]
  have hb : |Real.log (Z n)-(n : ℝ)*A|/(n : ℝ) ≤ e n := by
    apply (div_le_iff₀ hnR).2
    simpa only [mul_comm] using h n hn0
  exact hb.trans_lt (hN n (le_trans (le_max_left _ _) hn))

#print axioms normalized_log_tendsto_of_error
end SpectralRadiusUpperTail
