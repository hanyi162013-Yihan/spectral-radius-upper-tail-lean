import SpectralRadiusUpperTail.PolynomialExponentialBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma nat_rpow_div_tendsto_zero (q : ℝ) (hq : q < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)^q/(n : ℝ)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (show 0 < 1-q by linarith)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  dsimp only [Function.comp_apply]
  rw [show -(1-q) = q-1 by ring, Real.rpow_sub hnR, Real.rpow_one]

lemma scaled_power_rpow_div_tendsto_zero (k : ℕ → ℕ) (α q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α)) :
    Tendsto (fun n => (k n : ℝ)^q/(n : ℝ)) atTop (𝓝 0) := by
  have hh := (hk.rpow_const (Or.inr hq0)).mul (nat_rpow_div_tendsto_zero q hq1)
  rw [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [Real.div_rpow (Nat.cast_nonneg _) hnR.le]
  have hp : (n : ℝ)^q ≠ 0 := (Real.rpow_pos_of_pos hnR q).ne'
  field_simp

/-- A polynomial prefactor times exp(C k^q), q<1, is negligible at speed n
whenever k/n converges. This handles the k^(2/3) Schur error. -/
lemma schur_prefactor_le_exp (k : ℕ → ℕ) (α q C D : ℝ) (M : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hD : 0 < D)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, D*(n : ℝ)^M*Real.exp (C*(k n : ℝ)^q) ≤
      Real.exp ((n : ℝ)*ε) := by
  have ht := (scaled_power_rpow_div_tendsto_zero k α q hq0 hq1 hk).const_mul C
  rw [mul_zero] at ht
  have he := (tendsto_order.mp ht).2 (ε/2) (by positivity)
  filter_upwards [eventually_positive_polynomial_le_exp D hD M (ε/2) (by positivity),
    he, eventually_gt_atTop 0] with n hn he hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hb : C*(k n : ℝ)^q ≤ (n : ℝ)*(ε/2) := by
    have hh : (C*(k n : ℝ)^q)/(n : ℝ) < ε/2 := by simpa only [mul_div_assoc] using he
    have hx := (div_lt_iff₀ hnR).mp hh
    linarith
  calc
    _ ≤ Real.exp ((n : ℝ)*(ε/2))*Real.exp ((n : ℝ)*(ε/2)) :=
      mul_le_mul hn (Real.exp_le_exp.mpr hb) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms scaled_power_rpow_div_tendsto_zero
#print axioms schur_prefactor_le_exp
end SpectralRadiusUpperTail
