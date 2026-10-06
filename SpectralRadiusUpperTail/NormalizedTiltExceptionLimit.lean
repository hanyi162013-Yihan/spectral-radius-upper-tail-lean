import SpectralRadiusUpperTail.ChangeMeasure
import SpectralRadiusUpperTail.QuadraticExceptionRatio

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped ENNReal Topology

lemma normalizedTilt_real_exception_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Ω → ℝ≥0∞)
    (A : Set Ω) (hA : MeasurableSet A) (hw : ∀ x, w x ≤ 1)
    (Z : ℝ) (hZpos : 0 < Z) (hZ : (∫⁻ x, w x ∂μ) = ENNReal.ofReal Z) :
    (normalizedTilt μ w).real A ≤ μ.real A/Z := by
  have hh := normalizedTilt_exception_le μ w A hA hw
  rw [hZ] at hh
  have ht : (ENNReal.ofReal Z)⁻¹*μ A ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hZpos))) (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono ht hh
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hZpos.le,
    Measure.real,div_eq_mul_inv,mul_comm] using hr

lemma normalizedTilt_quadratic_exception_tendsto
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (w : (n : ℕ) → Ω n → ℝ≥0∞) (hw : ∀ n x, w n x ≤ 1)
    (Z : ℕ → ℝ) (hpos : ∀ n, 0 < Z n)
    (hZeq : ∀ n, (∫⁻ x, w n x ∂μ n) = ENNReal.ofReal (Z n))
    (a : ℝ) (hZ : Tendsto (fun n => Real.log (Z n)/(n : ℝ)) atTop (𝓝 a))
    (A : (n : ℕ) → Set (Ω n)) (hA : ∀ n, MeasurableSet (A n))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hbad : ∀ᶠ n in atTop, (μ n).real (A n) ≤ C*Real.exp (-c*(n : ℝ)^2)) :
    Tendsto (fun n => (normalizedTilt (μ n) (w n)).real (A n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) _
    (quadratic_exception_div_normalizer_tendsto Z hpos a hZ C c hC hc)
  filter_upwards [hbad] with n hn
  exact (normalizedTilt_real_exception_le (μ n) (w n) (A n) (hA n) (hw n)
    (Z n) (hpos n) (hZeq n)).trans (div_le_div_of_nonneg_right hn (hpos n).le)

#print axioms normalizedTilt_real_exception_le
#print axioms normalizedTilt_quadratic_exception_tendsto
end SpectralRadiusUpperTail
