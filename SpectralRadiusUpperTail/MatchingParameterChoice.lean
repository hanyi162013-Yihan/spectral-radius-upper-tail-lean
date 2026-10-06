import SpectralRadiusUpperTail.TiltCostAlgebra
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma matching_tilt_parameters (β r ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    ∃ b : ℝ, r < b ∧ ∃ s : ℝ, 0 < s ∧ r < b/(1+s) ∧
      lowerTiltCost β b s (2*s) s (2*s) < rate β r+ε := by
  have hrpos : 0 < r := by linarith
  have hrate : ContinuousAt (fun b : ℝ => rate β b) r := by
    unfold rate
    fun_prop (disch := positivity)
  have hnear := (tendsto_order.1 hrate.tendsto).2 (rate β r+ε/2) (by linarith)
  obtain ⟨d,hd,hdp⟩ := Metric.eventually_nhds_iff.1 hnear
  let b := r+d/2
  have hbr : r < b := by dsimp [b]; linarith
  have hb : rate β b < rate β r+ε/2 := by
    apply hdp
    dsimp [b]
    rw [Real.dist_eq]
    have he : r+d/2-r = d/2 := by ring
    rw [he,abs_of_pos (by positivity : 0 < d/2)]
    linarith
  have hc : ContinuousAt (fun s : ℝ => lowerTiltCost β b s (2*s) s (2*s)) 0 := by
    unfold lowerTiltCost
    fun_prop (disch := norm_num)
  have hcost0 : lowerTiltCost β b 0 (2*0) 0 (2*0) = rate β b := by
    simpa using lowerTiltCost_zero β b
  have hcgood := (tendsto_order.1 hc.tendsto).2 (rate β b+ε/2)
    (by rw [hcost0]; linarith)
  have hcenter : Tendsto (fun s : ℝ => b/(1+s)) (𝓝 0) (𝓝 b) := by
    have hh : ContinuousAt (fun s : ℝ => b/(1+s)) 0 := by fun_prop (disch := norm_num)
    simpa only [add_zero,div_one] using hh.tendsto
  have hcentergood := (tendsto_order.1 hcenter).1 r hbr
  obtain ⟨d',hd',hdp'⟩ := Metric.eventually_nhds_iff.1 (hcgood.and hcentergood)
  have hsmall : dist (d'/2) (0 : ℝ) < d' := by
    rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < d'/2)]
    linarith
  obtain ⟨hcost,hcent⟩ := hdp' hsmall
  exact ⟨b,hbr,d'/2,by positivity,hcent,by linarith⟩

#print axioms matching_tilt_parameters
end SpectralRadiusUpperTail
