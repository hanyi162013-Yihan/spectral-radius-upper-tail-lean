import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Metric

lemma disk_norm_bounds (b z : ℂ) (d : ℝ) (hz : z ∈ ball b d) :
    ‖b‖-d < ‖z‖ ∧ ‖z‖ < ‖b‖+d := by
  have hh : ‖z-b‖ < d := by simpa only [mem_ball,dist_eq_norm] using hz
  have h1 := norm_sub_norm_le b z
  rw [norm_sub_rev b z] at h1
  have h2 := norm_sub_norm_le z b
  constructor <;> linarith

lemma closed_disk_in_triple (b : ℂ) (d : ℝ) (hd : 0 < d) :
    closedBall b d ⊆ ball b (3*d) := by
  intro z hz
  have hh : dist z b ≤ d := hz
  change dist z b < 3*d
  linarith

#print axioms disk_norm_bounds
#print axioms closed_disk_in_triple
end SpectralRadiusUpperTail
