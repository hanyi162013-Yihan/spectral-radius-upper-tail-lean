import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- Moving the test radius by `1/n` does not change the logarithmic rate
of the real Ginibre density core. This lets a shrinking short interval
deliver the exact half-line lower rate without a separate liminf argument. -/
theorem realGinibreCoreDensity_moving_log_rate (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n : ℕ =>
      Real.log (realGinibreCoreDensity n (r+1/(n : ℝ)))/(n : ℝ))
      atTop (𝓝 (-rate 1 r)) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => r+1/(n : ℝ)) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hi
  have hlogshift : Tendsto (fun n : ℕ => Real.log (r+1/(n : ℝ)))
      atTop (𝓝 (Real.log r)) :=
    (Real.continuousAt_log hr.ne').tendsto.comp hshift
  have hlogdiff : Tendsto (fun n : ℕ =>
      Real.log (r+1/(n : ℝ))-Real.log r) atTop (𝓝 0) := by
    simpa using hlogshift.sub_const (Real.log r)
  have hcoef : Tendsto (fun n : ℕ => 1-1/(n : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  have hsqdiff : Tendsto (fun n : ℕ =>
      (r+1/(n : ℝ))^2-r^2) atTop (𝓝 0) := by
    have h := (hshift.pow 2).sub_const (r^2)
    rw [sub_self] at h
    exact h
  have hdiff : Tendsto (fun n : ℕ =>
      (1-1/(n : ℝ))*(Real.log (r+1/(n : ℝ))-Real.log r)-
        ((r+1/(n : ℝ))^2-r^2)/2) atTop (𝓝 0) := by
    simpa using (hcoef.mul hlogdiff).sub (hsqdiff.div_const 2)
  have hbase := realGinibreCoreDensity_log_rate r hr
  have hsum := hbase.add hdiff
  have hsum' : Tendsto (fun n : ℕ =>
      Real.log (realGinibreCoreDensity n r)/(n : ℝ) +
      ((1-1/(n : ℝ))*(Real.log (r+1/(n : ℝ))-Real.log r)-
        ((r+1/(n : ℝ))^2-r^2)/2)) atTop (𝓝 (-rate 1 r)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hshiftpos : 0 < r+1/(n : ℝ) := by positivity
  rw [realGinibreCoreDensity_log n hn (r+1/(n : ℝ)) hshiftpos,
    realGinibreCoreDensity_log n hn r hr]
  unfold realGinibreGammaLogCore
  ring

#print axioms realGinibreCoreDensity_moving_log_rate
end SpectralRadiusUpperTail
