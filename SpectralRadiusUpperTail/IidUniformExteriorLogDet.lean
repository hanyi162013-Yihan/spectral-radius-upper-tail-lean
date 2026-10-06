import SpectralRadiusUpperTail.UniformExteriorLogDetTest
import SpectralRadiusUpperTail.IidTraceResolvent

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Uniform exterior logdet convergence on every compact complex annulus. -/
lemma iid_uniform_exteriorLogDet_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r R ε : ℝ) (hr : 1 < r) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
        |normalizedComplexLogDet (normalizedIidMatrix x) z-Real.log ‖z‖| < ε})
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, htest⟩ := exists_uniform_complexLogDet_test r R ε
    (lt_trans (by norm_num) hr) hε
  have htrace := iid_trace_resolvent_probability μ c hc hexp hm hv r δ hr hδ
  have hnorm := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv 1 3 (by norm_num)
  simp only [pow_one] at hnorm
  have hsum := hnorm.add htrace
  simp only [zero_add] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [eventually_gt_atTop 0] with n hn
  let P := Measure.pi (fun _ : Fin n × Fin n => μ)
  apply (measureReal_mono (μ := P) (show
    {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      |normalizedComplexLogDet (normalizedIidMatrix x) z-Real.log ‖z‖| < ε} ⊆
      {x | (3 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedIidMatrix x)‖} ∪
        {x | ¬ matrixTraceControl (normalizedIidMatrix x) r δ} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedIidMatrix x)‖ ≤ 3 := by
    have hnot : ¬ (3 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (normalizedIidMatrix x)‖ :=
      fun h => hh (Or.inl h)
    exact (lt_of_not_ge hnot).le
  have ht : matrixTraceControl (normalizedIidMatrix x) r δ := by
    by_contra h
    exact hh (Or.inr h)
  exact hx (htest n hn (normalizedIidMatrix x) hA ht)

#print axioms iid_uniform_exteriorLogDet_probability
end SpectralRadiusUpperTail
