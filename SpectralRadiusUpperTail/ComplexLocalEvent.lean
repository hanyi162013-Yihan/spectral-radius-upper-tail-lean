import SpectralRadiusUpperTail.OutlierSpectralRadius
import SpectralRadiusUpperTail.GaussianSourceEvents

namespace SpectralRadiusUpperTail
open MeasureTheory Metric

/-- The normalized iid array has an actual spectral point in an open disk. -/
def complexLocalEigenvalueEvent (n : ℕ) (z : ℂ) (ε : ℝ) :
    Set (Fin n → Fin n → ℂ) :=
  {x | ∃ w ∈ ball z ε, w ∈ spectrum ℂ (normalizedArray x)}

lemma complexLocalEigenvalueEvent_measurable (n : ℕ) (z : ℂ) (ε : ℝ) :
    MeasurableSet (complexLocalEigenvalueEvent n z ε) := by
  have he : complexLocalEigenvalueEvent n z ε =
      ⋃ q : ℚ, ⋃ (_ : (q : ℝ) < ε),
        {x | ∃ w ∈ closedBall z (q : ℝ), w ∈ spectrum ℂ (normalizedArray x)} := by
    ext x
    simp only [complexLocalEigenvalueEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨w, hw, hs⟩
      obtain ⟨q, hq, hqε⟩ := exists_rat_btwn (show dist w z < ε from hw)
      exact ⟨q, hqε, w, hq.le, hs⟩
    · rintro ⟨q, hq, w, hw, hs⟩
      exact ⟨w, lt_of_le_of_lt hw hq, hs⟩
  rw [he]
  exact MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun _ =>
    (measurableSet_matrix_outlier_event n z (q : ℝ)).preimage measurable_normalizedArray))

lemma complexLocalEigenvalueEvent_mono {n : ℕ} {z w : ℂ} {ε δ : ℝ}
    (h : ball w δ ⊆ ball z ε) :
    complexLocalEigenvalueEvent n w δ ⊆ complexLocalEigenvalueEvent n z ε := by
  rintro x ⟨v, hv, hs⟩
  exact ⟨v, h hv, hs⟩

lemma complexLocalEigenvalueEvent_subset_radius (n : ℕ) (z : ℂ) (ε : ℝ) :
    complexLocalEigenvalueEvent n z ε ⊆
      {x | ‖z‖-ε < (spectralRadius ℂ (normalizedArray x)).toReal} := by
  rintro x ⟨w, hw, hs⟩
  have hd : ‖w-z‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hw
  have ht := norm_sub_le w (w-z)
  simp only [sub_sub_cancel] at ht
  have hr := complex_eigenvalue_le_spectralRadius (normalizedArray x) w hs
  change ‖z‖-ε < (spectralRadius ℂ (normalizedArray x)).toReal
  linarith

#print axioms complexLocalEigenvalueEvent_measurable
#print axioms complexLocalEigenvalueEvent_subset_radius
end SpectralRadiusUpperTail
