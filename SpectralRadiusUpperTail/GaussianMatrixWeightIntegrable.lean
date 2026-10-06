import SpectralRadiusUpperTail.GaussianMatrixWeight
import SpectralRadiusUpperTail.SpectralTiltTarget
import SpectralRadiusUpperTail.TailDenominator

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ}

lemma gaussianMatrixWeight_measurable (a : ℝ) (v t : Fin n → 𝕂) :
    Measurable (gaussianMatrixWeight a v t) := by
  unfold gaussianMatrixWeight
  fun_prop

lemma gaussianMatrixWeight_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v t : Fin n → 𝕂) :
    Integrable (gaussianMatrixWeight a v t)
      (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) := by
  apply Integrable.of_bound (gaussianMatrixWeight_measurable a v t).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (gaussianMatrixWeight_pos a v t x).le]
  exact gaussianMatrixWeight_le_one a ha v t x

lemma gaussianMatrixWeight_integral_pos (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (v t : Fin n → 𝕂) :
    0 < ∫ x : Fin n → Fin n → 𝕂, gaussianMatrixWeight a v t x
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)) := by
  exact integral_exp_pos (gaussianMatrixWeight_integrable μ a ha v t)

lemma gaussianSpectralWeight_joint_continuous (a : ℝ) (b : 𝕂) :
    Continuous (fun p : (Fin n → 𝕂) × (Fin n → Fin n → 𝕂) =>
      gaussianMatrixWeight a p.1 (spectralTiltTarget b (zeroExtendVector p.1)) p.2) := by
  simp only [gaussianMatrixWeight,spectralTiltTarget,zeroExtendVector_fin]
  fun_prop

#print axioms gaussianMatrixWeight_measurable
#print axioms gaussianMatrixWeight_integrable
#print axioms gaussianMatrixWeight_integral_pos
#print axioms gaussianSpectralWeight_joint_continuous
end SpectralRadiusUpperTail
