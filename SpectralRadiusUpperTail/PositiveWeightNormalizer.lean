import SpectralRadiusUpperTail.GaussianMatrixWeightIntegrable
import SpectralRadiusUpperTail.NormalizedTiltProductEvent

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

lemma positiveWeight_lintegral_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [NeZero μ] (w : Ω → ℝ) (hi : Integrable w μ)
    (hp : ∀ x, 0 < w x) :
    (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≠ ∞ := by
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (hp x).le))
  rw [← he]
  have hpos : 0 < ∫ x, w x ∂μ := integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi |>.2 (by
    have hs : Function.support w = Set.univ := by
      ext x
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact ne_of_gt (hp x)
    rw [hs]
    exact bot_lt_iff_ne_bot.mpr (NeZero.ne (μ Set.univ)))
  exact ⟨ne_of_gt (ENNReal.ofReal_pos.2 hpos),ENNReal.ofReal_ne_top⟩

#print axioms positiveWeight_lintegral_bounds
end SpectralRadiusUpperTail
