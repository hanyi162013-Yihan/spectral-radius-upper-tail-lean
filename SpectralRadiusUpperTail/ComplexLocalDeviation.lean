import SpectralRadiusUpperTail.ComplexLocalLower
import SpectralRadiusUpperTail.ExponentialLowerLiminf

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The universal part of the manuscript's local eigenvalue theorem:
an exterior disk has lower rate I₂ at its nearest radial boundary. -/
theorem complex_local_eigenvalue_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0)
    (hexp : ∃ c : ℝ, 0 < c ∧ Integrable (fun x : ℂ => Real.exp (c*‖x‖^2)) μ)
    (z : ℂ) (ε : ℝ) (hε : 0 < ε) (hgap : ε < ‖z‖-1) :
    -rate 2 (‖z‖-ε) ≤ liminf (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n z ε))/(n : ℝ)) atTop := by
  obtain ⟨c, hc, hi⟩ := hexp
  have hi' : Integrable (fun x : ℂ => Real.exp (4*(c/4)*‖x‖^2)) μ := by
    simpa only [show 4*(c/4) = c by ring] using hi
  apply log_liminf_of_exponential_lower _ _ (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
  intro δ hδ
  exact complex_local_exponential_lower μ hm hv hp (c/4) (by positivity) hi' z ε hε hgap δ hδ

/-- Under the sharp planar MGF bound the local upper and lower rates match.
Square-exponential integrability follows from the entry assumptions. -/
theorem complex_sharp_local_exponential_bounds
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0) (hmgf : SharpPlanarMGF μ)
    (z : ℂ) (ε : ℝ) (hε : 0 < ε) (hgap : ε < ‖z‖-1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((n : ℝ)*(-rate 2 (‖z‖-ε)-δ)) ≤
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          (complexLocalEigenvalueEvent n z ε) ∧
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
          (complexLocalEigenvalueEvent n z ε) ≤
        Real.exp ((n : ℝ)*(-rate 2 (‖z‖-ε)+δ)) := by
  have hexp : Integrable (fun x : ℂ => Real.exp (4*(1/100)*‖x‖^2)) μ := by
    convert (sharp_planar_squareExp μ hmgf).1 using 1 <;> norm_num
  have h2 := squareExp_norm_pow_integrable μ (4*(1/100)) (by norm_num) hexp 2
  have hconv := cutoff_concentration_transfer μ (4*(1/100)) (by norm_num) hexp h2
    (cutoff_convex_concentration_proved μ)
  have hupper := complex_sharp_upper_of_concentration μ (4*(1/100)) (by norm_num) hexp
    hm hv hp (fun u => (hmgf u).1) (fun u => (hmgf u).2) (‖z‖-ε) (by linarith) ?_ δ hδ
  · filter_upwards [hupper, complex_local_exponential_lower μ hm hv hp
        (1/100) (by norm_num) hexp z ε hε hgap δ hδ] with n hu hl
    refine ⟨hl, (measureReal_mono (μ := Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) ?_).trans hu⟩
    intro x hx
    have hr : ‖z‖-ε < (spectralRadius ℂ (normalizedArray x)).toReal :=
      complexLocalEigenvalueEvent_subset_radius n z ε hx
    exact hr.le
  · intro R s d hs hd
    obtain ⟨C, hC, q, hq, ht⟩ := complex_bulk_concentration_of_convex_concentration μ h2 hconv s d hs hd
    refine ⟨C, hC, q, hq, ?_⟩
    filter_upwards [ht] with n hn w _ _
    exact hn w

/-- The exact fixed-disk LDP, for actual eigenvalues of the iid matrix.
It needs neither rotational invariance nor any real Gaussian input. -/
theorem complex_local_eigenvalue_deviations
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0) (hmgf : SharpPlanarMGF μ)
    (z : ℂ) (ε : ℝ) (hε : 0 < ε) (hgap : ε < ‖z‖-1) :
    Tendsto (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n z ε))/(n : ℝ)) atTop (𝓝 (-rate 2 (‖z‖-ε))) := by
  apply tendsto_log_of_exponential_bounds
  exact complex_sharp_local_exponential_bounds μ hm hv hp hmgf z ε hε hgap

/-- First n tends to infinity, then the radius of the disk tends to zero. -/
theorem complex_local_eigenvalue_small_disk_limit
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0) (hmgf : SharpPlanarMGF μ)
    (z : ℂ) (hz : 1 < ‖z‖) :
    Tendsto (fun ε : ℝ => limUnder atTop (fun n => Real.log
      ((Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))).real
        (complexLocalEigenvalueEvent n z ε))/(n : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 (-rate 2 ‖z‖)) := by
  have hz0 : ‖z‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz)
  have hc : ContinuousAt (fun ε : ℝ => -rate 2 (‖z‖-ε)) 0 := by
    unfold rate
    fun_prop (disch := simpa only [sub_zero] using hz0)
  have ht : Tendsto (fun ε : ℝ => -rate 2 (‖z‖-ε)) (𝓝[>] (0 : ℝ)) (𝓝 (-rate 2 ‖z‖)) := by
    simpa only [sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < ‖z‖-1 :=
    (eventually_lt_nhds (by linarith : (0 : ℝ) < ‖z‖-1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hgap
  exact (complex_local_eigenvalue_deviations μ hm hv hp hmgf z ε hε hgap).limUnder_eq.symm

#print axioms complex_local_eigenvalue_lower
#print axioms complex_sharp_local_exponential_bounds
#print axioms complex_local_eigenvalue_deviations
#print axioms complex_local_eigenvalue_small_disk_limit
end SpectralRadiusUpperTail
