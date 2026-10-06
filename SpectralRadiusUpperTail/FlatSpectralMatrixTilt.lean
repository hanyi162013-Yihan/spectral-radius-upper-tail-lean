import SpectralRadiusUpperTail.FlatSpectralJointTilt
import SpectralRadiusUpperTail.PositiveWeightNormalizer
import SpectralRadiusUpperTail.NormalizedTiltMarginal

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ} {L : ℝ}

noncomputable def flatSpectralMatrixWeight
    (ν : Measure (flatUnitDirections 𝕂 n L)) (a : ℝ) (b : 𝕂)
    (x : Fin n → Fin n → 𝕂) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (flatSpectralJointWeight a b (v,x)) ∂ν

noncomputable def flatSpectralMatrixTilt (μ : Measure 𝕂)
    (ν : Measure (flatUnitDirections 𝕂 n L)) (a : ℝ) (b : 𝕂) :
    Measure (Fin n → Fin n → 𝕂) :=
  normalizedTilt (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))
    (flatSpectralMatrixWeight ν a b)

lemma flatSpectralJointTilt_matrix_marginal (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) :
    (flatSpectralJointTilt μ ν a b).map Prod.snd = flatSpectralMatrixTilt μ ν a b := by
  have hZ := positiveWeight_lintegral_bounds
    (ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))
    (flatSpectralJointWeight a b) (flatSpectralJointWeight_integrable μ ν a ha b)
    (fun p => gaussianMatrixWeight_pos a _ _ _)
  exact normalizedTilt_prod_snd _ _ ν _ _
    ((flatSpectralJointWeight_continuous a b).measurable.ennreal_ofReal) hZ.1

lemma flatSpectralMatrixTilt_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) :
    IsProbabilityMeasure (flatSpectralMatrixTilt μ ν a b) := by
  letI := flatSpectralJointTilt_probability μ ν a ha b
  rw [← flatSpectralJointTilt_matrix_marginal μ ν a ha b]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

lemma flatSpectralMatrixTilt_event (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂)
    (A : Set (Fin n → Fin n → 𝕂)) (hA : MeasurableSet A) :
    flatSpectralMatrixTilt μ ν a b A =
      flatSpectralJointTilt μ ν a b (Set.univ ×ˢ A) := by
  rw [← flatSpectralJointTilt_matrix_marginal μ ν a ha b,Measure.map_apply measurable_snd hA]
  congr 1
  ext p
  simp

#print axioms flatSpectralMatrixWeight
#print axioms flatSpectralMatrixTilt
#print axioms flatSpectralJointTilt_matrix_marginal
#print axioms flatSpectralMatrixTilt_probability
#print axioms flatSpectralMatrixTilt_event
end SpectralRadiusUpperTail
