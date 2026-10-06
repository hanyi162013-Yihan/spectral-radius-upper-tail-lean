import SpectralRadiusUpperTail.HalfGammaLower
import SpectralRadiusUpperTail.MomentExponentTransfer
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- Stirling at a moving half-integer argument, expressed relative to the
original dimension `n`. -/
lemma half_gamma_moving_log_rate (m : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hmTop : Tendsto m atTop atTop)
    (hmRatio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ =>
      Real.log (Real.Gamma ((m n : ℝ)/2+1))/(n : ℝ) -
        ((m n : ℝ)/(n : ℝ))*Real.log ((n : ℝ)/2)/2)
      atTop (𝓝 (c/2*(Real.log c-1))) := by
  have hgamma := (half_gamma_rate_limit.comp hmTop).mul hmRatio
  have hlog := (Real.continuousAt_log hc.ne').tendsto.comp hmRatio
  have hratioLog := hmRatio.mul hlog
  have hsum := hgamma.add (hratioLog.div_const 2)
  have hlimit : (-1/2 : ℝ)*c+c*Real.log c/2 =
      c/2*(Real.log c-1) := by ring
  rw [hlimit] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0,
    hmTop.eventually (eventually_gt_atTop 0)] with n hn hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmR : (0 : ℝ) < m n := Nat.cast_pos.mpr hm
  have hlogeq : Real.log ((m n : ℝ)/2)-Real.log ((n : ℝ)/2) =
      Real.log ((m n : ℝ)/(n : ℝ)) := by
    rw [Real.log_div hmR.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hnR.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hmR.ne' hnR.ne']
    ring
  dsimp only [Function.comp_apply]
  have hnne : (n : ℝ) ≠ 0 := hnR.ne'
  have hmne : (m n : ℝ) ≠ 0 := hmR.ne'
  field_simp [hnne, hmne]
  nlinarith [hlogeq]

/-- The Gamma ratio controlling the dominant weighted real-Ginibre density
has the exact candidate power-moment exponent for `k/n → α`. -/
theorem realGinibre_weighted_gamma_log_rate (k : ℕ → ℕ) (α : ℝ)
    (hα : 0 < α)
    (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (𝓝 α)) :
    Tendsto (fun n : ℕ =>
      Real.log (Real.Gamma (((n+2*k n : ℕ) : ℝ)/2+1))/(n : ℝ) -
        Real.log (Real.Gamma ((n : ℝ)/2+1))/(n : ℝ) -
        ((k n : ℝ)/(n : ℝ))*Real.log ((n : ℝ)/2))
      atTop (𝓝 (powerRate 1 α)) := by
  let m : ℕ → ℕ := fun n => n+2*k n
  have hmTop : Tendsto m atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [m]
    omega
  have hmRatio : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop
      (𝓝 (1+2*α)) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hh := hconst.add (hk.const_mul 2)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := by positivity
    dsimp [m]
    push_cast
    field_simp
  have hM := half_gamma_moving_log_rate m (1+2*α)
    (by linarith) hmTop hmRatio
  have hN := half_gamma_rate_limit
  have hdiff := hM.sub hN
  have hlimit : (1+2*α)/2*(Real.log (1+2*α)-1)-(-1/2) =
      powerRate 1 α := by unfold powerRate; ring
  rw [hlimit] at hdiff
  apply hdiff.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by positivity
  dsimp [m]
  push_cast
  field_simp
  ring

#print axioms half_gamma_moving_log_rate
#print axioms realGinibre_weighted_gamma_log_rate
end SpectralRadiusUpperTail
