import SpectralRadiusUpperTail.DiscardedSquareMean
import SpectralRadiusUpperTail.IntegralSqrtBound
import SpectralRadiusUpperTail.ProductRowEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

lemma product_discarded_energy_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ) (R : ℝ) (hi : Integrable (fun x : E => ‖x‖^2) μ) :
    Integrable (fun x : Fin N → E => ∑ i, discardedSquare R (x i)) (Measure.pi (fun _ => μ)) := by
  apply integrable_finsetSum
  intro i hi'
  exact (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable (discardedSquare_integrable μ R hi)

lemma product_discarded_energy_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ) (R : ℝ) (hi : Integrable (fun x : E => ‖x‖^2) μ) :
    (∫ x : Fin N → E, ∑ i, discardedSquare R (x i) ∂Measure.pi (fun _ => μ)) =
      (N : ℝ)*(∫ x, discardedSquare R x ∂μ) := by
  have hcoord (i : Fin N) : Integrable (fun x : Fin N → E => discardedSquare R (x i))
      (Measure.pi (fun _ => μ)) :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable
      (discardedSquare_integrable μ R hi)
  rw [integral_finsetSum _ (fun i _ => hcoord i)]
  simp_rw [integral_product_coordinate μ _ _ (discardedSquare_measurable R).aestronglyMeasurable]
  simp

lemma product_discarded_energy_sqrt (μ : Measure E) [IsProbabilityMeasure μ]
    (N : ℕ) (R : ℝ) (hi : Integrable (fun x : E => ‖x‖^2) μ) :
    Integrable (fun x : Fin N → E => Real.sqrt (∑ i, discardedSquare R (x i)))
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin N → E, Real.sqrt (∑ i, discardedSquare R (x i)) ∂Measure.pi (fun _ => μ)) ≤
      Real.sqrt ((N : ℝ)*(∫ x, discardedSquare R x ∂μ)) := by
  have hm : Measurable (fun x : Fin N → E => ∑ i, discardedSquare R (x i)) := by
    apply Finset.measurable_sum
    intro i hi'
    exact (discardedSquare_measurable R).comp (measurable_pi_apply i)
  have hh := integral_sqrt_bound (Measure.pi (fun _ : Fin N => μ)) _ hm
    (product_discarded_energy_integrable μ N R hi)
    (fun x => Finset.sum_nonneg (fun i _ => (discardedSquare_bounds R (x i)).1))
  rw [product_discarded_energy_mean μ N R hi] at hh
  exact hh

#print axioms product_discarded_energy_integrable
#print axioms product_discarded_energy_mean
#print axioms product_discarded_energy_sqrt
end SpectralRadiusUpperTail
