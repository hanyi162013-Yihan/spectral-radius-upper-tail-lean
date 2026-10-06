import SpectralRadiusUpperTail.TiltCostAlgebra
import SpectralRadiusUpperTail.ComplexLocalEvent

namespace SpectralRadiusUpperTail
open Filter Metric
open scoped Topology

lemma complex_point_tilt_parameters (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ lowerTiltCost 2 ((s+1)*r) s (2*s) s (2*s) < rate 2 r+ε := by
  have hc : ContinuousAt (fun s : ℝ => lowerTiltCost 2 ((s+1)*r) s (2*s) s (2*s)) 0 := by
    unfold lowerTiltCost
    fun_prop (disch := positivity)
  have hzero : lowerTiltCost 2 ((0+1)*r) 0 (2*0) 0 (2*0) = rate 2 r := by
    simpa using lowerTiltCost_zero 2 r
  have he := (tendsto_order.1 hc.tendsto).2 (rate 2 r+ε) (by rw [hzero]; linarith)
  obtain ⟨d, hd, hdp⟩ := Metric.eventually_nhds_iff.1 he
  refine ⟨d/2, by positivity, hdp ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < d/2)]
  linarith

/-- A small disk about a radial interior point sits inside the prescribed disk. -/
lemma complex_local_radial_disk (z : ℂ) (ε t : ℝ)
    (hε : 0 < ε) (hgap : ε < ‖z‖-1) (ht : 0 < t) (htε : t < ε) :
    ∃ w : ℂ, ‖w‖ = ‖z‖-ε+t ∧
      ball w (t/2) ⊆ ball z ε := by
  have hz : 0 < ‖z‖ := by linarith
  let a := (‖z‖-ε+t)/‖z‖
  have ha : 0 < a := div_pos (by linarith) hz
  have ha1 : a < 1 := by
    apply (div_lt_one hz).mpr
    linarith
  refine ⟨a • z, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    exact div_mul_cancel₀ _ hz.ne'
  · have hd : dist (a • z) z = ε-t := by
      rw [dist_eq_norm, show a • z-z = (a-1) • z by simp [sub_smul],
        norm_smul, Real.norm_eq_abs, abs_of_neg (by linarith : a-1 < 0)]
      dsimp [a]
      field_simp [hz.ne']
      <;> ring
    intro v hv
    have hh := dist_triangle v (a • z) z
    rw [hd] at hh
    have hvd : dist v (a • z) < t/2 := hv
    change dist v z < ε
    linarith

#print axioms complex_point_tilt_parameters
#print axioms complex_local_radial_disk
end SpectralRadiusUpperTail
