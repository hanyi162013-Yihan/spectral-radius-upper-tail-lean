import SpectralRadiusUpperTail.ComplexPointLower

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- Optimize the pointwise lower rate over an exterior disk. -/
theorem complex_local_exponential_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (z : ℂ) (δ : ℝ) (hδ : 0 < δ) (hgap : δ < ‖z‖-1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((n : ℝ)*(-rate 2 (‖z‖-δ)-ε)) ≤
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n z δ) := by
  let a := ‖z‖-δ
  have ha : 1 < a := by dsimp [a]; linarith
  have hcont : ContinuousAt (fun t : ℝ => rate 2 (a+t)) 0 := by
    unfold rate
    fun_prop (disch := positivity)
  have he := (tendsto_order.1 hcont.tendsto).2 (rate 2 a+ε/2) (by simp only [add_zero]; linarith)
  obtain ⟨d, hd, hdp⟩ := Metric.eventually_nhds_iff.1 he
  let t := min d δ/2
  have ht : 0 < t := div_pos (lt_min hd hδ) (by norm_num)
  have htd : t < d := by have := min_le_left d δ; dsimp [t]; linarith
  have htδ : t < δ := by have := min_le_right d δ; dsimp [t]; linarith
  have hcost : rate 2 (a+t) < rate 2 a+ε/2 :=
    hdp (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht] using htd)
  obtain ⟨w, hwn, hball⟩ := complex_local_radial_disk z δ t hδ hgap ht htδ
  have hw : 1 < ‖w‖ := by rw [hwn]; dsimp [a] at ha; linarith
  filter_upwards [complex_point_exponential_lower μ hm hv hp c hc hexp
    w hw (t/2) (by positivity) (ε/2) (by positivity)] with n hn
  apply le_trans _ (measureReal_mono (μ := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (complexLocalEigenvalueEvent_mono hball))
  apply le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))) hn
  rw [hwn]
  change -rate 2 a-ε ≤ -rate 2 (a+t)-ε/2
  linarith

#print axioms complex_local_exponential_lower
end SpectralRadiusUpperTail
