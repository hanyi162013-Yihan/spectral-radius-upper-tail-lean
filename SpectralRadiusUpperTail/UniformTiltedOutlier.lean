import SpectralRadiusUpperTail.GaussianTiltedOutlier
import SpectralRadiusUpperTail.FlatUnitDirections
import SpectralRadiusUpperTail.UniformFromSequences

namespace SpectralRadiusUpperTail
open MeasureTheory Filter Metric
open scoped Topology BigOperators Matrix

lemma complex_gaussianTilted_outlier_uniform (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℂ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 1 ≤ L)
    (b : ℂ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖b‖-1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ w : Fin n → ℂ, w ∈ flatUnitDirections ℂ n L →
      (gaussianTiltedMatrixLaw μ η (zeroExtendVector w)
        (rankOneTiltTarget (n := n) η b (zeroExtendVector w))).real
        {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ (normalizedArray x)} < ε := by
  have (n : ℕ) : Nonempty (flatUnitDirections ℂ n L) :=
    (flatUnitDirections_nonempty ℂ n L hL).to_subtype
  let f := fun n (w : flatUnitDirections ℂ n L) =>
    (gaussianTiltedMatrixLaw μ η (zeroExtendVector w.val)
      (rankOneTiltTarget (n := n) η b (zeroExtendVector w.val))).real
      {x | ¬ ∃ z ∈ closedBall b d, z ∈ spectrum ℂ (normalizedArray x)}
  have hf : ∀ w : (n : ℕ) → flatUnitDirections ℂ n L,
      Tendsto (fun n => f n (w n)) atTop (𝓝 0) := by
    intro w
    apply complex_gaussianTilted_outlier_probability μ hm hvar hpseudo c hc hexp
      η L hη (by linarith) (fun n => zeroExtendVector (w n).val)
    · intro n
      simpa only [zeroExtendVector_fin] using (w n).property.1
    · intro n hn
      simpa only [zeroExtendVector_fin] using (w n).property.2.1 hn
    · intro n j
      simpa only [zeroExtendVector_fin] using (w n).property.2.2 j
    · exact hd
    · exact hgap
  have hu := uniform_small_of_all_sequences (fun n => flatUnitDirections ℂ n L) f hf ε hε
  filter_upwards [hu] with n hn w hw
  exact hn ⟨w,hw⟩

lemma real_gaussianTilted_outlier_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℝ, x ∂μ) = 0) (hvar : (∫ x : ℝ, ‖x‖^2 ∂μ) = 1)
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : ℝ => Real.exp (4*c*‖x‖^2)) μ)
    (η L : ℝ) (hη : 0 < η) (hL : 1 ≤ L)
    (b : ℝ) (d : ℝ) (hd : 0 < d) (hgap : 3*d < ‖(b : ℂ)‖-1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ w : Fin n → ℝ, w ∈ flatUnitDirections ℝ n L →
      (gaussianTiltedMatrixLaw μ (2*η) (zeroExtendVector w)
        (rankOneTiltTarget (n := n) η b (zeroExtendVector w))).real
        {x | ¬ ∃ z ∈ closedBall (b : ℂ) d, z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)} < ε := by
  have (n : ℕ) : Nonempty (flatUnitDirections ℝ n L) :=
    (flatUnitDirections_nonempty ℝ n L hL).to_subtype
  let f := fun n (w : flatUnitDirections ℝ n L) =>
    (gaussianTiltedMatrixLaw μ (2*η) (zeroExtendVector w.val)
      (rankOneTiltTarget (n := n) η b (zeroExtendVector w.val))).real
      {x | ¬ ∃ z ∈ closedBall (b : ℂ) d, z ∈ spectrum ℂ ((normalizedArray x).map Complex.ofRealHom)}
  have hf : ∀ w : (n : ℕ) → flatUnitDirections ℝ n L,
      Tendsto (fun n => f n (w n)) atTop (𝓝 0) := by
    intro w
    apply real_gaussianTilted_outlier_probability μ hm hvar c hc hexp
      η L hη (by linarith) (fun n => zeroExtendVector (w n).val)
    · intro n
      simpa only [zeroExtendVector_fin] using (w n).property.1
    · intro n hn
      simpa only [zeroExtendVector_fin] using (w n).property.2.1 hn
    · intro n j
      simpa only [zeroExtendVector_fin] using (w n).property.2.2 j
    · exact hd
    · exact hgap
  have hu := uniform_small_of_all_sequences (fun n => flatUnitDirections ℝ n L) f hf ε hε
  filter_upwards [hu] with n hn w hw
  exact hn ⟨w,hw⟩

#print axioms complex_gaussianTilted_outlier_uniform
#print axioms real_gaussianTilted_outlier_uniform
end SpectralRadiusUpperTail
