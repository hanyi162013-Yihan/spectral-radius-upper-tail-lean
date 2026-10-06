import SpectralRadiusUpperTail.GaussianMatrixWeightIntegrable
import SpectralRadiusUpperTail.FlatUnitDirections
import SpectralRadiusUpperTail.ChangeMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ} {L : ℝ}

noncomputable def flatSpectralJointWeight (a : ℝ) (b : 𝕂)
    (p : (flatUnitDirections 𝕂 n L) × (Fin n → Fin n → 𝕂)) : ℝ :=
  gaussianMatrixWeight a p.1.val (spectralTiltTarget b (zeroExtendVector p.1.val)) p.2

noncomputable def flatSpectralJointTilt (μ : Measure 𝕂)
    (ν : Measure (flatUnitDirections 𝕂 n L)) (a : ℝ) (b : 𝕂) :
    Measure ((flatUnitDirections 𝕂 n L) × (Fin n → Fin n → 𝕂)) :=
  normalizedTilt (ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))))
    (fun p => ENNReal.ofReal (flatSpectralJointWeight a b p))

lemma flatSpectralJointWeight_continuous (a : ℝ) (b : 𝕂) :
    Continuous (flatSpectralJointWeight (n := n) (L := L) a b) := by
  have hv (j : Fin n) : Continuous (fun p : (flatUnitDirections 𝕂 n L) × (Fin n → Fin n → 𝕂) => p.1.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
  have hx (i j : Fin n) : Continuous (fun p : (flatUnitDirections 𝕂 n L) × (Fin n → Fin n → 𝕂) => p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  unfold flatSpectralJointWeight gaussianMatrixWeight
  simp only [spectralTiltTarget,zeroExtendVector_fin]
  fun_prop

lemma flatSpectralJointWeight_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) :
    Integrable (flatSpectralJointWeight a b)
      (ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))) := by
  apply Integrable.of_bound (flatSpectralJointWeight_continuous a b).measurable.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [flatSpectralJointWeight]
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianMatrixWeight_pos a _ _ _).le]
  exact gaussianMatrixWeight_le_one a ha _ _ _

lemma flatSpectralJointTilt_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) :
    IsProbabilityMeasure (flatSpectralJointTilt μ ν a b) := by
  have hi := flatSpectralJointWeight_integrable μ ν a ha b
  have hp : 0 < ∫ p, flatSpectralJointWeight a b p
      ∂ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) :=
    integral_exp_pos hi
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun p => (gaussianMatrixWeight_pos a _ _ _).le))
  apply normalizedTilt_probability
  · rw [← he]
    exact ne_of_gt (ENNReal.ofReal_pos.2 hp)
  · rw [← he]
    exact ENNReal.ofReal_ne_top

#print axioms flatSpectralJointWeight
#print axioms flatSpectralJointTilt
#print axioms flatSpectralJointWeight_continuous
#print axioms flatSpectralJointWeight_integrable
#print axioms flatSpectralJointTilt_probability
end SpectralRadiusUpperTail
