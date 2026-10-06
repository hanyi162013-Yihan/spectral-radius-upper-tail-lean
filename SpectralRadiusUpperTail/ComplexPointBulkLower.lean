import SpectralRadiusUpperTail.ComplexBulkMeanUpperUniform
import SpectralRadiusUpperTail.LowerMeanFromProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology ComplexOrder MatrixOrder

lemma normalized_complexRegularizedLogDet_ge_exterior {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hz : z ∈ resolventSet ℂ A) :
    2*normalizedComplexLogDet A z ≤ complexRegularizedLogDet A z s/(n : ℝ) := by
  have hdet : (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A).det ≠ 0 := by
    simpa only [resolventSet, Set.mem_setOf_eq, Algebra.algebraMap_eq_smul_one,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using hz
  have hh := (posSemidef_shift_det_lower _
    (Matrix.posSemidef_conjTranspose_mul_self (A-z • 1)) s hs).2
  have hpos : 0 < ‖((A-z • 1).conjTranspose*(A-z • 1)).det‖ := by
    rw [matrix_gram_det_norm, complex_shift_det_norm_comm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hdet)
  have hl := Real.log_le_log hpos hh
  rw [matrix_gram_det_norm, complex_shift_det_norm_comm, Real.log_pow] at hl
  have hd := div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)
  simpa only [normalizedComplexLogDet, complexRegularizedLogDet, mul_div_assoc] using! hd

lemma iid_complex_point_regularizedLogDet_lower_probability
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (z : ℂ) (s ε : ℝ) (hz : 1 < ‖z‖) (hs : 0 ≤ s) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) <
        2*Real.log ‖z‖-ε}) atTop (𝓝 0) := by
  have hlog := iid_uniform_exteriorLogDet_probability μ c hc hexp hm hv
    ‖z‖ ‖z‖ (ε/2) hz (by positivity)
  have htrace := iid_trace_resolvent_probability μ c hc hexp hm hv ‖z‖ 1 hz (by norm_num)
  have hsum := hlog.add htrace
  simp only [zero_add] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin n × Fin n => μ)) (show
    {x | complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) < 2*Real.log ‖z‖-ε} ⊆
      {x | ¬ ∀ w : ℂ, ‖z‖ ≤ ‖w‖ → ‖w‖ ≤ ‖z‖ →
        |normalizedComplexLogDet (normalizedIidMatrix x) w-Real.log ‖w‖| < ε/2} ∪
      {x | ¬ matrixTraceControl (normalizedIidMatrix x) ‖z‖ 1} from ?_)).trans
    (measureReal_union_le _ _)
  intro x hx
  by_contra hh
  have ht : matrixTraceControl (normalizedIidMatrix x) ‖z‖ 1 := by
    by_contra h
    exact hh (Or.inr h)
  have hl : ∀ w : ℂ, ‖z‖ ≤ ‖w‖ → ‖w‖ ≤ ‖z‖ →
      |normalizedComplexLogDet (normalizedIidMatrix x) w-Real.log ‖w‖| < ε/2 := by
    by_contra h
    exact hh (Or.inl h)
  have hlo := (abs_lt.mp (hl z le_rfl le_rfl)).1
  have hcompare := normalized_complexRegularizedLogDet_ge_exterior
    (normalizedIidMatrix x) z s hs (ht z le_rfl).1
  change complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ) < 2*Real.log ‖z‖-ε at hx
  linarith

lemma complex_point_bulk_logDet_mean_lower
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (z : ℂ) (s ε : ℝ) (hz : 1 < ‖z‖) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 2*Real.log ‖z‖-ε ≤
      ∫ x : Fin n → Fin n → ℂ, regularizedResidualLogDet x z s/(n : ℝ)
        ∂Measure.pi (fun _ => Measure.pi (fun _ => μ)) := by
  simp only [iid_complex_regularizedResidualLogDet_integral]
  apply eventually_integral_lower_of_probability (fun n => Fin n × Fin n → ℂ)
    (fun n => Measure.pi (fun _ : Fin n × Fin n => μ))
    (fun n x => complexRegularizedLogDet (normalizedIidMatrix x) z s/(n : ℝ))
    (fun n => ((complexRegularizedLogDet_measurable n z s).comp
      (normalizedIidMatrix_continuous n).measurable).div_const _) _
    (min 0 (Real.log s)) (2*Real.log ‖z‖) _ _ ε hε
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact iid_complexRegularizedLogDet_integrable μ (squareExp_norm_pow_integrable μ c hc hexp 4)
      n hn z s hs
  · intro n x
    by_cases hn : n = 0
    · subst n
      simpa only [Nat.cast_zero, div_zero] using min_le_left (0 : ℝ) (Real.log s)
    · exact (min_le_right _ _).trans (normalized_complexRegularizedLogDet_floor
        (Nat.pos_of_ne_zero hn) (normalizedIidMatrix x) z s hs)
  · intro δ hδ
    exact iid_complex_point_regularizedLogDet_lower_probability μ c hc hexp hm hv z s δ hz hs.le hδ

#print axioms normalized_complexRegularizedLogDet_ge_exterior
#print axioms iid_complex_point_regularizedLogDet_lower_probability
#print axioms complex_point_bulk_logDet_mean_lower
end SpectralRadiusUpperTail
