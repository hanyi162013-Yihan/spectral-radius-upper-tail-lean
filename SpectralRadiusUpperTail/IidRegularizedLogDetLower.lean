import SpectralRadiusUpperTail.IidExteriorLogDet
import SpectralRadiusUpperTail.MatrixRegularizedLogDet

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_regularizedLogDet_lower_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b s ε : ℝ) (hb : 1 < b) (hs : 0 ≤ s) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) < 2*Real.log b-ε})
      atTop (𝓝 0) := by
  have hlog := iid_exteriorLogDet_probability μ c hc hexp hm hv b (ε/2) hb (by positivity)
  have htrace := iid_trace_resolvent_probability μ c hc hexp hm hv b 1 hb (by norm_num)
  have hsum := hlog.add htrace
  simp only [zero_add] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  let P := Measure.pi (fun _ : Fin n × Fin n => μ)
  apply (measureReal_mono (μ := P) (show
    {x | matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) < 2*Real.log b-ε} ⊆
      {x | ε/2 ≤ |normalizedExteriorLogDet (normalizedIidMatrix x) b-Real.log b|} ∪
        {x | ¬ matrixTraceControl (normalizedIidMatrix x) b 1} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have hlogx : |normalizedExteriorLogDet (normalizedIidMatrix x) b-Real.log b| < ε/2 :=
    lt_of_not_ge (fun h => hh (Or.inl h))
  have ht : matrixTraceControl (normalizedIidMatrix x) b 1 := by
    by_contra h
    exact hh (Or.inr h)
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hnorm : b ≤ ‖(b : ℂ)‖ := by simp [abs_of_pos hb0]
  have hcompare := normalized_matrixRegularizedLogDet_ge_exterior (normalizedIidMatrix x)
    b s hs (ht b hnorm).1
  change matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) < 2*Real.log b-ε at hx
  have hlo := (abs_lt.mp hlogx).1
  linarith

#print axioms iid_regularizedLogDet_lower_probability
end SpectralRadiusUpperTail
