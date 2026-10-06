import SpectralRadiusUpperTail.ResolventLogDetGap
import SpectralRadiusUpperTail.IidExteriorLogDet

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma iid_regularizedLogDet_upper_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (b : ℝ) (hb : 1 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℝ, 0 ≤ s → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | 2*Real.log b+s*M^2+ε < matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)})
        atTop (𝓝 0) := by
  obtain ⟨M, hM, hbase⟩ := iid_exterior_resolvent_probability μ c hc hexp hm hv b hb
  refine ⟨M, hM, ?_⟩
  intro s hs ε hε
  have hlog := iid_exteriorLogDet_probability μ c hc hexp hm hv b (ε/2) hb (by positivity)
  have hsum := hbase.add hlog
  simp only [zero_add] at hsum
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsum
  filter_upwards [eventually_gt_atTop 0] with n hn
  let P := Measure.pi (fun _ : Fin n × Fin n => μ)
  apply (measureReal_mono (μ := P) (show
    {x | 2*Real.log b+s*M^2+ε < matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ)} ⊆
      {x | ¬ matrixExteriorControl (normalizedIidMatrix x) b M} ∪
        {x | ε/2 ≤ |normalizedExteriorLogDet (normalizedIidMatrix x) b-Real.log b|} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have hext : matrixExteriorControl (normalizedIidMatrix x) b M := by
    by_contra h
    exact hh (Or.inl h)
  have hclose : |normalizedExteriorLogDet (normalizedIidMatrix x) b-Real.log b| < ε/2 := by
    exact lt_of_not_ge (fun h => hh (Or.inr h))
  have hbn : b ≤ ‖(b : ℂ)‖ := by simp [abs_of_pos (lt_trans (by norm_num) hb)]
  have hd := matrixRegularizedLogDet_le_exterior (normalizedIidMatrix x) b s M hs hM
    (hext b hbn).1 (hext b hbn).2
  have hdiv := div_le_div_of_nonneg_right hd (Nat.cast_nonneg n)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hu : matrixRegularizedLogDet (normalizedIidMatrix x) b s/(n : ℝ) ≤
      2*normalizedExteriorLogDet (normalizedIidMatrix x) b+s*M^2 := by
    convert! hdiv using 1
    unfold normalizedExteriorLogDet
    field_simp
  have habs := (abs_lt.mp hclose).2
  change 2*Real.log b+s*M^2+ε < _ at hx
  linarith

#print axioms iid_regularizedLogDet_upper_probability
end SpectralRadiusUpperTail
