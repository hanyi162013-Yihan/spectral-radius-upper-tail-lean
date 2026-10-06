import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail

lemma inverse_denominator_increment (a d e : ℝ) (ha : 0 < a) (hd : a ≤ d) (he : 0 ≤ e) :
    0 ≤ 1/d-1/(d+e) ∧ 1/d-1/(d+e) ≤ e/a^2 := by
  have hdpos : 0 < d := ha.trans_le hd
  have hde : 0 < d+e := by positivity
  have hid : 1/d-1/(d+e) = e/(d*(d+e)) := by field_simp; ring
  rw [hid]
  constructor
  · positivity
  · apply div_le_div₀ he le_rfl (sq_pos_of_pos ha)
    have hh := mul_le_mul hd (show a ≤ d+e by linarith) ha.le hdpos.le
    nlinarith only [hh]

lemma scalar_regression_denominator_shift {𝕂 : Type*} [RCLike 𝕂]
    (b s : 𝕂) (a d : ℝ) (ha : 0 < a) (hd : a ≤ d) :
    ‖(1/d : ℝ) • (star b*s)-(1/(d+‖b‖^2) : ℝ) • (star b*s)‖ ≤
      (‖s‖/a^2)*‖b‖^3 := by
  obtain ⟨hn, hb⟩ := inverse_denominator_increment a d (‖b‖^2) ha hd (sq_nonneg _)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn, norm_mul, norm_star]
  calc
    _ ≤ (‖b‖^2/a^2)*(‖b‖*‖s‖) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- Adding the current coefficient to the tail denominator costs only a cubic term. -/
theorem regression_denominator_shift {𝕂 : Type*} [RCLike 𝕂]
    (m b s : 𝕂) (a d R : ℝ) (ha : 0 < a) (hd : a ≤ d)
    (hR : ‖m-(1/d : ℝ) • (star b*s)‖ ≤ R) :
    ‖m-(1/(d+‖b‖^2) : ℝ) • (star b*s)‖ ≤ R+(‖s‖/a^2)*‖b‖^3 := by
  have ht := norm_add_le (m-(1/d : ℝ) • (star b*s))
    ((1/d : ℝ) • (star b*s)-(1/(d+‖b‖^2) : ℝ) • (star b*s))
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hR (scalar_regression_denominator_shift b s a d ha hd))

#print axioms regression_denominator_shift
end SpectralRadiusUpperTail
