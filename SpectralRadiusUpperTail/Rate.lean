import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
noncomputable def rate (β r : ℝ) : ℝ := β/2*(r^2-1-2*Real.log r)
noncomputable def powerRate (β α : ℝ) : ℝ :=
  β/2*((1+2*α/β)*Real.log (1+2*α/β)-2*α/β)

lemma entropy_gap_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x*Real.log (x/y)-x+y := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have hcancel : x*(y/x-1) = y-x := by
    field_simp [ne_of_gt hx]
  rw [hcancel] at hm
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
  nlinarith

theorem rate_nonneg (β r : ℝ) (hβ : 0 ≤ β) (hr : 0 < r) : 0 ≤ rate β r := by
  have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos hr)
  rw [Real.log_pow] at h
  norm_num at h
  unfold rate
  apply mul_nonneg (by positivity)
  nlinarith

theorem rate_pos (β r : ℝ) (hβ : 0 < β) (hr : 1 < r) : 0 < rate β r := by
  have hr₀ : 0 < r := by linarith
  have hsq : 1 < r^2 := by nlinarith
  have h := Real.log_lt_sub_one_of_pos (sq_pos_of_pos hr₀) (ne_of_gt hsq)
  rw [Real.log_pow] at h
  norm_num at h
  unfold rate
  apply mul_pos (by positivity)
  nlinarith

theorem rate_two_eq (r : ℝ) : rate 2 r = 2 * rate 1 r := by unfold rate; ring

theorem dual_at_optimizer (β r : ℝ) (hβ : β ≠ 0) :
    powerRate β (β/2*(r^2-1))-2*(β/2*(r^2-1))*Real.log r = -rate β r := by
  have harg : 1+2*(β/2*(r^2-1))/β = r^2 := by field_simp [hβ]; ring
  unfold powerRate rate
  rw [harg, Real.log_pow]
  field_simp
  <;> ring

/-- The entropy identity supplies the global dual bound, not just stationarity. -/
theorem dual_lower_bound (β r α : ℝ) (hβ : 0 < β) (hr : 0 < r)
    (hα : 0 ≤ α) :
    -rate β r ≤ powerRate β α - 2*α*Real.log r := by
  have hx : 0 < 1+2*α/β := by positivity
  have hy : 0 < r^2 := sq_pos_of_pos hr
  have hg := entropy_gap_nonneg (1+2*α/β) (r^2) hx hy
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy), Real.log_pow] at hg
  norm_num at hg
  have hm := mul_nonneg (show 0 ≤ β/2 by positivity) hg
  have hid : powerRate β α-2*α*Real.log r+rate β r =
      β/2*((1+2*α/β)*(Real.log (1+2*α/β)-2*Real.log r)
        -(1+2*α/β)+r^2) := by
    unfold powerRate rate
    field_simp
    <;> ring
  linarith

theorem optimizer_positive (β r : ℝ) (hβ : 0 < β) (hr : 1 < r) :
    0 < β/2*(r^2-1) := by
  apply mul_pos (by positivity)
  nlinarith

/-- Exact minimization over the positive moment-power parameter. -/
theorem dual_minimum (β r : ℝ) (hβ : 0 < β) (hr : 1 < r) :
    (∀ α > 0, -rate β r ≤ powerRate β α-2*α*Real.log r) ∧
    (∃ α > 0, powerRate β α-2*α*Real.log r = -rate β r) := by
  constructor
  · intro α hα
    exact dual_lower_bound β r α hβ (by linarith) hα.le
  · exact ⟨β/2*(r^2-1), optimizer_positive β r hβ hr,
      dual_at_optimizer β r (ne_of_gt hβ)⟩

theorem rate_strict_mono (β a b : ℝ) (hβ : 0 < β) (ha : 1 ≤ a) (hab : a < b) :
    rate β a < rate β b := by
  have ha₀ : 0 < a := by linarith
  have hb₀ : 0 < b := lt_trans ha₀ hab
  have hquot : 1 < b/a := (one_lt_div ha₀).2 hab
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hb₀ ha₀) (ne_of_gt hquot)
  rw [Real.log_div (ne_of_gt hb₀) (ne_of_gt ha₀)] at hlog
  have hm := mul_lt_mul_of_pos_left hlog ha₀
  have hc : a*(b/a-1)=b-a := by field_simp [ne_of_gt ha₀]
  rw [hc] at hm
  have hd : 0 < b-a := sub_pos.mpr hab
  have hquad : 0 ≤ (b-a)*(a+b-2) := mul_nonneg hd.le (by linarith)
  have hl : 0 ≤ Real.log b-Real.log a :=
    sub_nonneg.mpr (Real.log_le_log ha₀ hab.le)
  have hprod : 0 ≤ (a-1)*(Real.log b-Real.log a) :=
    mul_nonneg (by linarith) hl
  have hgap : a^2-1-2*Real.log a < b^2-1-2*Real.log b := by nlinarith
  exact mul_lt_mul_of_pos_left hgap (show 0 < β/2 by positivity)

#print axioms entropy_gap_nonneg
#print axioms rate_pos
#print axioms dual_at_optimizer
#print axioms dual_minimum
#print axioms rate_strict_mono
end SpectralRadiusUpperTail
