import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma integrable_shifted_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → E) (b : E)
    (hF : Measurable (fun x => ‖F x-b‖^2))
    (h2 : Integrable (fun x => ‖F x‖^2) μ) :
    Integrable (fun x => ‖F x-b‖^2) μ := by
  apply ((h2.const_mul 2).add (integrable_const (2*‖b‖^2))).mono'
    hF.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖F x-b‖^2 ≤ 2*‖F x‖^2+2*‖b‖^2
  have hh := norm_sub_le (F x) b
  have hs := sq_nonneg (‖F x‖-‖b‖)
  have hsq := (sq_le_sq₀ (norm_nonneg (F x-b))
    (add_nonneg (norm_nonneg (F x)) (norm_nonneg b))).mpr hh
  nlinarith

#print axioms integrable_shifted_norm_sq
end SpectralRadiusUpperTail
