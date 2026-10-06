import SpectralRadiusUpperTail.GaussianSequentialCoupling
import SpectralRadiusUpperTail.DoobPathIntegrability

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Every actual coordinate of the fixed paired history is integrable on both
sides. The source estimate uses its bounded partial weight, before any stopping. -/
theorem gaussianSequentialRowLaw_coordinate_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : Integrable (fun x : 𝕂 => x) μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n ≤ N) (i : Fin n) :
    Integrable (fun s : Fin n → 𝕂 × 𝕂 => (s i).1) (gaussianSequentialRowLaw μ v a N t n) ∧
    Integrable (fun s : Fin n → 𝕂 × 𝕂 => (s i).2) (gaussianSequentialRowLaw μ v a N t n) := by
  have hi : Integrable (fun s : Fin n → 𝕂 => s i) (Measure.pi (fun _ : Fin n => μ)) := by
    convert! (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hX using 1
  refine ⟨?_, ?_⟩
  · exact doobCoupledPathLaw_source_integrable μ N _
      (gaussianRevealedWeight_measurable μ v a N t)
      (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
      (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
      (revealedWeight_rec μ _ _ N t)
      (fun n _ s => futureWeight_le_one μ _ _ (gaussianSoftWeight_le_one a ha) _ _)
      n hn (fun s => s i) hi
  · exact doobCoupledPathLaw_comparator_integrable μ N _
      (gaussianRevealedWeight_measurable μ v a N t)
      (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
      (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
      (revealedWeight_rec μ _ _ N t) n (fun s => s i) hi

/-- Integrability of the actual new source-minus-comparator increment under
the history/kernel joint law follows from the next finite path law. -/
theorem gaussianSequentialJoint_difference_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : Integrable (fun x : 𝕂 => x) μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    Integrable (fun z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) => z.2.1-z.2.2)
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) := by
  have hi := gaussianSequentialRowLaw_coordinate_integrable μ hX v a ha N t (n+1)
    (by omega) (0 : Fin (n+1))
  have hd := hi.1.sub hi.2
  rw [gaussianSequentialRowLaw_succ] at hd
  have hh := hd.comp_measurable (measurable_fin_cons n)
  simpa only [Function.comp_def, Pi.sub_apply, Fin.cons_zero] using hh

#print axioms gaussianSequentialRowLaw_coordinate_integrable
#print axioms gaussianSequentialJoint_difference_integrable
end SpectralRadiusUpperTail
