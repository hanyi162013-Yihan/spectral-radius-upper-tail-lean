import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- The target quarter-power logarithmic concentration scale. -/
noncomputable def logQuarterRate (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ ((3 : ℝ)/4) / (n : ℝ) ^ ((1 : ℝ)/4)

lemma logQuarterRate_tendsto : Tendsto logQuarterRate atTop (𝓝 0) := by
  exact (isLittleO_log_rpow_rpow_atTop ((3 : ℝ)/4)
    (by norm_num : (0 : ℝ) < 1/4)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

lemma logQuarterRate_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ logQuarterRate n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (Real.rpow_nonneg (Real.log_nonneg hn') _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Exact identity used to compare the confidence threshold with the target rate. -/
lemma logQuarterRate_square (n : ℕ) (hn : 1 ≤ n) :
    (logQuarterRate n)^2*Real.sqrt (n : ℝ) = (Real.sqrt (Real.log (n : ℝ)))^3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hp : ((n : ℝ)^((1 : ℝ)/4))^2 = Real.sqrt (n : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hn0.le, Real.sqrt_eq_rpow]
    norm_num
  have hq : (Real.log (n : ℝ)^((3 : ℝ)/4))^2 =
      (Real.sqrt (Real.log (n : ℝ)))^3 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hl, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast _ 3, ← Real.rpow_mul hl]
    norm_num
  rw [logQuarterRate, div_pow, hp, hq]
  exact div_mul_cancel₀ _ (Real.sqrt_pos.mpr hn0).ne'

#print axioms logQuarterRate_tendsto
#print axioms logQuarterRate_square
end SpectralRadiusUpperTail
