import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma outlier_disk_parameters (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1) :
    ∃ r L ε : ℝ, 1 < r ∧ 0 < L ∧ 0 < ε ∧ r ≤ ‖b‖-3*d ∧ ‖b‖+3*d ≤ L ∧
      ‖b‖*L*ε ≤ d/8 := by
  let r := (1+‖b‖-3*d)/2
  let L := ‖b‖+3*d+1
  let K := ‖b‖*L
  have hL : 0 < L := by dsimp [L]; positivity
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg b) hL.le
  let ε := d/(8*(K+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨r,L,ε,?_,hL,hε,?_,?_,?_⟩
  · dsimp [r]
    linarith
  · dsimp [r]
    linarith
  · dsimp [L]
    linarith
  · change K*(d/(8*(K+1))) ≤ d/8
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 8*(K+1))).mpr
    nlinarith

#print axioms outlier_disk_parameters
end SpectralRadiusUpperTail
