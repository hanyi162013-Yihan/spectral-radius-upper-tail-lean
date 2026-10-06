import SpectralRadiusUpperTail.IidPowerOperatorLimit
import SpectralRadiusUpperTail.MatrixExteriorPowerBound
import SpectralRadiusUpperTail.ChooseResolventPower

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology BigOperators

/-- Actual complex iid matrices have uniformly bounded Euclidean resolvents
outside every fixed disk of radius greater than one, with probability tending to one.
No spectral-radius lower bound or circular-law input is used. -/
lemma iid_exterior_resolvent_probability (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : ℂ => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : ℂ, z ∂μ) = 0) (hv : (∫ z : ℂ, ‖z‖^2 ∂μ) = 1)
    (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ =>
      (Measure.pi (fun _ : Fin n × Fin n => μ)).real
        {x | ¬ matrixExteriorControl (normalizedIidMatrix x) r C}) atTop (𝓝 0) := by
  obtain ⟨m,hm1,hmp⟩ := exists_resolvent_power r hr
  let C := max 1 ((2*∑ j ∈ Finset.range m, (3/r)^j)/r)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  have h1 := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv 1 3 (by norm_num)
  have h2 := normalizedPower_operator_probability_tendsto μ c hc hexp hm hv m (m+2) (by linarith)
  have ht := h1.add h2
  simp only [zero_add] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  apply le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
  intro x hx
  change (3 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((normalizedIidMatrix x)^1)‖) ∨
    ((m+2 : ℝ) ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((normalizedIidMatrix x)^m)‖)
  by_contra hb
  push_neg at hb
  apply hx
  apply matrixExteriorControl_of_power hn (normalizedIidMatrix x) r 3
    (lt_trans (by norm_num) hr) m
  · simpa only [pow_one] using hb.1.le
  · exact hb.2.le.trans hmp

#print axioms iid_exterior_resolvent_probability
end SpectralRadiusUpperTail
