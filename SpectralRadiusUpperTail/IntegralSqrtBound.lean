import SpectralRadiusUpperTail.Centering
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma integral_sqrt_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℝ)
    (hF : Measurable F) (hi : Integrable F μ) (hn : ∀ x, 0 ≤ F x) :
    Integrable (fun x => Real.sqrt (F x)) μ ∧
      (∫ x, Real.sqrt (F x) ∂μ) ≤ Real.sqrt (∫ x, F x ∂μ) := by
  have hs : Integrable (fun x => Real.sqrt (F x)) μ := by
    apply ((integrable_const (1 : ℝ)).add hi).mono' hF.sqrt.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (F x) ≤ 1+F x
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith [hn x]
    · nlinarith [hn x,sq_nonneg (F x)]
  have hsq : Integrable (fun x => ‖Real.sqrt (F x)‖^2) μ := by
    simpa only [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hn _)] using hi
  have he := integral_centered_norm_sq μ (fun x => Real.sqrt (F x)) hs hsq
  have hp : 0 ≤ ∫ x, ‖Real.sqrt (F x)-∫ y, Real.sqrt (F y) ∂μ‖^2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [he] at hp
  simp only [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hn _)] at hp
  refine ⟨hs,?_⟩
  apply (Real.le_sqrt (integral_nonneg (fun _ => Real.sqrt_nonneg _))
    (integral_nonneg hn)).mpr
  linarith

#print axioms integral_sqrt_bound
end SpectralRadiusUpperTail
