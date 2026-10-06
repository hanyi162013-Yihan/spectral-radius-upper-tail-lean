import SpectralRadiusUpperTail.UniformFromSequences
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

lemma integral_tendsto_zero_of_uniform_small
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : (n : ℕ) → Ω n → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x, ‖f n x‖ ≤ ε) :
    Tendsto (fun n => ∫ x, f n x ∂μ n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 (h (ε/2) (by positivity))
  refine ⟨N,fun n hn => ?_⟩
  have hb := norm_integral_le_of_norm_le_const (μ := μ n) (f := f n) (C := ε/2)
    (Eventually.of_forall (hN n hn))
  rw [dist_zero_right]
  have he : (μ n).real Set.univ = 1 := by simp [Measure.real]
  rw [he,mul_one] at hb
  linarith

#print axioms integral_tendsto_zero_of_uniform_small
end SpectralRadiusUpperTail
