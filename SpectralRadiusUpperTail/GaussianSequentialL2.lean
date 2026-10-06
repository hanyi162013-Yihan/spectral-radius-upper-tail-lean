import SpectralRadiusUpperTail.GaussianSequentialIntegrability
import SpectralRadiusUpperTail.RowNormalizerBound

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Both coordinates of the actual finite coupled history are square
integrable. The source statement uses the bounded actual Doob weight. -/
theorem gaussianSequentialRowLaw_coordinate_memLp_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n ≤ N) (i : Fin n) :
    MemLp (fun s : Fin n → 𝕂 × 𝕂 => (s i).1) 2 (gaussianSequentialRowLaw μ v a N t n) ∧
      MemLp (fun s : Fin n → 𝕂 × 𝕂 => (s i).2) 2 (gaussianSequentialRowLaw μ v a N t n) := by
  have h2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hi : Integrable (fun s : Fin n → 𝕂 => ‖s i‖^2) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable h2
  constructor
  · apply (memLp_two_iff_integrable_sq_norm
      (measurable_fst.comp (measurable_pi_apply i)).aestronglyMeasurable).mpr
    exact doobCoupledPathLaw_source_integrable μ N _
      (gaussianRevealedWeight_measurable μ v a N t)
      (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
      (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
      (revealedWeight_rec μ _ _ N t)
      (fun n _ s => futureWeight_le_one μ _ _ (gaussianSoftWeight_le_one a ha) _ _)
      n hn (fun s => ‖s i‖^2) hi
  · apply (memLp_two_iff_integrable_sq_norm
      (measurable_snd.comp (measurable_pi_apply i)).aestronglyMeasurable).mpr
    exact doobCoupledPathLaw_comparator_integrable μ N _
      (gaussianRevealedWeight_measurable μ v a N t)
      (fun n _ => gaussianRevealedWeight_ne_zero μ v a N t n)
      (fun n _ => gaussianRevealedWeight_ne_top μ v a ha N t n)
      (revealedWeight_rec μ _ _ N t) n (fun s => ‖s i‖^2) hi

/-- Actual square integrability under the history/next-pair joint law. -/
theorem gaussianSequentialJoint_difference_memLp_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) (v : ℕ → 𝕂) (a : ℝ) (ha : 0 < a)
    (N : ℕ) (t : 𝕂) (n : ℕ) (hn : n < N) :
    MemLp (fun z : (Fin n → 𝕂 × 𝕂) × (𝕂 × 𝕂) => z.2.1-z.2.2) 2
      ((gaussianSequentialRowLaw μ v a N t n) ⊗ₘ gaussianSequentialKernel μ v a N t n) := by
  have hi := gaussianSequentialRowLaw_coordinate_memLp_two μ hX v a ha N t (n+1)
    (by omega) (0 : Fin (n+1))
  have hd := hi.1.sub hi.2
  rw [gaussianSequentialRowLaw_succ] at hd
  have hh := hd.comp_of_map (measurable_fin_cons n).aemeasurable
  simpa only [Function.comp_def, Pi.sub_apply, Fin.cons_zero] using hh

#print axioms gaussianSequentialJoint_difference_memLp_two
end SpectralRadiusUpperTail
