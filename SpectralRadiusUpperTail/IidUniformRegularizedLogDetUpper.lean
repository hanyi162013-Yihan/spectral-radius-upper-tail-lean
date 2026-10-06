import SpectralRadiusUpperTail.ComplexRegularizedLogDetGap
import SpectralRadiusUpperTail.IidUniformExteriorLogDet

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_uniform_regularizedLogDet_upper_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ R s : ℝ, 0 ≤ s → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) ≤
            2*Real.log ‖z‖+s*M^2+ε}) atTop (𝓝 0) := by
  obtain ⟨M, hM, hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv r hr
  refine ⟨M, hM, ?_⟩
  intro R s hs ε hε
  have hlog := iid_uniform_exteriorLogDet_probability μ c hc hexp hm hv r R (ε/2) hr (by positivity)
  have hsum := hbase.add hlog
  simp only [zero_add] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [eventually_gt_atTop 0] with n hn
  let P := Measure.pi (fun _ : Fin n × Fin n => μ)
  apply (measureReal_mono (μ := P) (show
    {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) ≤ 2*Real.log ‖z‖+s*M^2+ε} ⊆
      {x | ¬ matrixExteriorControl (normalizedIidMatrix x) r M} ∪
        {x | ¬ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
          |normalizedComplexLogDet (normalizedIidMatrix x) z-Real.log ‖z‖| < ε/2} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have hext : matrixExteriorControl (normalizedIidMatrix x) r M := by
    by_contra h
    exact hh (Or.inl h)
  have hclose : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R →
      |normalizedComplexLogDet (normalizedIidMatrix x) z-Real.log ‖z‖| < ε/2 := by
    by_contra h
    exact hh (Or.inr h)
  apply hx
  intro z hrz hzR
  have hu := normalized_complexRegularizedLogDet_le_exterior hn (normalizedIidMatrix x) z s M hs hM
    (hext z hrz).1 (hext z hrz).2
  have hl := (abs_lt.mp (hclose z hrz hzR)).2
  linarith

#print axioms iid_uniform_regularizedLogDet_upper_probability
end SpectralRadiusUpperTail
