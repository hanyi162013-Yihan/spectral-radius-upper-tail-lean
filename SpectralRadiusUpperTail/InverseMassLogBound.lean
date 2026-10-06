import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped ENNReal

lemma inverse_mass_le_exp_of_log_lower (p : ℝ≥0∞) (hp : p ≠ ∞)
    (hp0 : 0 < p.toReal) (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hlog : -ε ≤ Real.log p.toReal/(n : ℝ)) :
    p⁻¹ ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*ε)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := (le_div_iff₀ hnpos).mp hlog
  have hr : p.toReal⁻¹ ≤ Real.exp ((n : ℝ)*ε) := by
    apply (Real.log_le_iff_le_exp (inv_pos.mpr hp0)).mp
    rw [Real.log_inv]
    nlinarith
  calc
    p⁻¹ = ENNReal.ofReal (p.toReal⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hp0,ENNReal.ofReal_toReal hp]
    _ ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*ε)) := ENNReal.ofReal_le_ofReal hr

#print axioms inverse_mass_le_exp_of_log_lower
end SpectralRadiusUpperTail
