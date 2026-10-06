import SpectralRadiusUpperTail.TiltCostAlgebra
import Mathlib.Topology.MetricSpace.Basic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma exists_positive_tilt_parameters (β b r ε : ℝ) (hb : r < b) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ r < b/(1+s) ∧ lowerTiltCost β b s s s s < rate β b+ε := by
  have hc := (tendsto_order.1 (lowerTiltCost_continuousAt_zero β b).tendsto).2
    (rate β b+ε) (by rw [lowerTiltCost_zero]; linarith)
  have ht : Tendsto (fun s : ℝ => b/(1+s)) (𝓝 0) (𝓝 b) := by
    have hh : ContinuousAt (fun s : ℝ => b/(1+s)) 0 := by fun_prop (disch := norm_num)
    simpa only [add_zero,div_one] using hh.tendsto
  have hr := (tendsto_order.1 ht).1 r hb
  obtain ⟨d,hd,hdp⟩ := Metric.eventually_nhds_iff.1 (hr.and hc)
  have hsmall : dist (d/2) (0 : ℝ) < d := by
    rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < d/2)]
    linarith
  exact ⟨d/2,by positivity,(hdp hsmall).1,(hdp hsmall).2⟩

#print axioms exists_positive_tilt_parameters
end SpectralRadiusUpperTail
