import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma likelihood_cost_of_log_bounds (n : ℕ) (hn : 0 < n)
    (W : ℝ≥0∞) (I Z κ S A : ℝ) (hI : 0 < I) (hZ : 0 < Z)
    (hW : W ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*κ))*ENNReal.ofReal I)
    (hS : Real.log I/(n : ℝ) ≤ S) (hA : A ≤ Real.log Z/(n : ℝ)) :
    W/ENNReal.ofReal Z ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*(κ+S-A))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hSi := (div_le_iff₀ hnpos).mp hS
  have hAi := (le_div_iff₀ hnpos).mp hA
  have hr : Real.exp ((n : ℝ)*κ)*I/Z ≤ Real.exp ((n : ℝ)*(κ+S-A)) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_div (by positivity) hZ.ne',Real.log_mul (Real.exp_ne_zero _) hI.ne',Real.log_exp]
    nlinarith
  calc
    W/ENNReal.ofReal Z ≤ (ENNReal.ofReal (Real.exp ((n : ℝ)*κ))*ENNReal.ofReal I)/ENNReal.ofReal Z :=
      ENNReal.div_le_div_right hW _
    _ = ENNReal.ofReal (Real.exp ((n : ℝ)*κ)*I/Z) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_div_of_pos hZ]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hr

#print axioms likelihood_cost_of_log_bounds
end SpectralRadiusUpperTail
