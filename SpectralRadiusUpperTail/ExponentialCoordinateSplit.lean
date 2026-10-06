import SpectralRadiusUpperTail.ExponentialWitnessFirstCoordinate
import Mathlib.MeasureTheory.Measure.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_normalized_integral_split (m : ℕ) (i : Fin (m+1)) (N u : ℝ)
    (h : Fin (m+1) → ℝ) :
    (∫⁻ y : Fin (m+1) → ℝ,
      ENNReal.ofReal (Real.exp (-(N/u)*((∑ j, h j*y j)/(∑ j, y j))))
      ∂Measure.pi (fun _ => expMeasure (1/2))) =
    ∫⁻ y : Fin m → ℝ, ∫⁻ y₀ : ℝ,
      exponentialWitnessIntegrand N u (h i) (fun j => h (i.succAbove j)) y₀ y
        ∂expMeasure (1/2) ∂Measure.pi (fun _ => expMeasure (1/2)) := by
  letI : IsProbabilityMeasure (expMeasure (1/2)) := isProbabilityMeasure_expMeasure (by norm_num)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) i
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => expMeasure (1/2)) i
  have hf := exponentialWitnessIntegrand_measurable m N u (h i) (fun j => h (i.succAbove j))
  have hh := hp.lintegral_comp hf
  have he : (fun y : Fin (m+1) → ℝ =>
      exponentialWitnessIntegrand N u (h i) (fun j => h (i.succAbove j)) (e y).1 (e y).2) =
      (fun y : Fin (m+1) → ℝ => ENNReal.ofReal (Real.exp (-(N/u)*((∑ j, h j*y j)/(∑ j, y j))))) := by
    funext y
    unfold exponentialWitnessIntegrand
    rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ i]
    rfl
  change (∫⁻ y, exponentialWitnessIntegrand N u (h i) (fun j => h (i.succAbove j))
      (e y).1 (e y).2 ∂Measure.pi (fun _ => expMeasure (1/2))) = _ at hh
  rw [he] at hh
  rw [hh]
  exact lintegral_prod_symm _ hf.aemeasurable

#print axioms exponential_normalized_integral_split
end SpectralRadiusUpperTail
