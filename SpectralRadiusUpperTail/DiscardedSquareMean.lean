import SpectralRadiusUpperTail.DiscardedSquareMGF

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma discardedSquare_integrable (μ : Measure E) (R : ℝ)
    (hi : Integrable (fun x : E => ‖x‖^2) μ) : Integrable (discardedSquare (E := E) R) μ := by
  apply hi.mono' (discardedSquare_measurable R).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (discardedSquare_bounds R x).1]
  exact (discardedSquare_bounds R x).2

lemma discardedSquare_mean_identity (μ : Measure E) (R : ℝ)
    (hi : Integrable (fun x : E => ‖x‖^2) μ) :
    (∫ x, discardedSquare R x ∂μ) = (∫ x, ‖x‖^2 ∂μ)-∫ x in closedBall 0 R, ‖x‖^2 ∂μ := by
  have he (x : E) : discardedSquare R x = ‖x‖^2-
      (closedBall (0 : E) R).indicator (fun x => ‖x‖^2) x := by
    by_cases hx : ‖x‖ ≤ R
    · simp [discardedSquare,not_lt.mpr hx,mem_closedBall,dist_zero_right,hx]
    · simp [discardedSquare,lt_of_not_ge hx,mem_closedBall,dist_zero_right,hx]
  simp_rw [he]
  have hfi : Integrable ((closedBall (0 : E) R).indicator (fun x => ‖x‖^2)) μ :=
    hi.indicator measurableSet_closedBall
  rw [integral_sub hi hfi,integral_indicator measurableSet_closedBall]

lemma discardedSquare_mean_tendsto_zero (μ : Measure E)
    (hi : Integrable (fun x : E => ‖x‖^2) μ) :
    Tendsto (fun k : ℕ => ∫ x, discardedSquare (k : ℝ) x ∂μ) atTop (𝓝 0) := by
  simp_rw [discardedSquare_mean_identity μ _ hi]
  have ht : Tendsto (fun _ : ℕ => ∫ x : E, ‖x‖^2 ∂μ) atTop (𝓝 (∫ x : E, ‖x‖^2 ∂μ)) :=
    tendsto_const_nhds
  simpa using ht.sub (integral_closedBall_nat_tendsto μ _ hi)

#print axioms discardedSquare_integrable
#print axioms discardedSquare_mean_identity
#print axioms discardedSquare_mean_tendsto_zero
end SpectralRadiusUpperTail
