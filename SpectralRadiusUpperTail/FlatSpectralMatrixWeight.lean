import SpectralRadiusUpperTail.FlatSpectralMatrixTilt
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂] {n : ℕ} {L : ℝ}

lemma flatSpectralMatrixWeight_measurable
    (ν : Measure (flatUnitDirections 𝕂 n L)) [SFinite ν] (a : ℝ) (b : 𝕂) :
    Measurable (flatSpectralMatrixWeight ν a b) := by
  exact ((flatSpectralJointWeight_continuous a b).measurable.ennreal_ofReal).lintegral_prod_left'

lemma flatSpectralMatrixWeight_le_one
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) (x : Fin n → Fin n → 𝕂) :
    flatSpectralMatrixWeight ν a b x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _v, (1 : ℝ≥0∞) ∂ν := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_one.mpr (gaussianMatrixWeight_le_one a ha _ _ _)
    _ = 1 := by simp

lemma flatSpectralMatrixWeight_normalizer (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) :
    (∫⁻ x, flatSpectralMatrixWeight ν a b x
      ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ))) =
    ENNReal.ofReal (∫ p, flatSpectralJointWeight a b p
      ∂ν.prod (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => μ)))) := by
  unfold flatSpectralMatrixWeight
  rw [← lintegral_prod_symm _ ((flatSpectralJointWeight_continuous a b).measurable.ennreal_ofReal).aemeasurable]
  exact (ofReal_integral_eq_lintegral_ofReal (flatSpectralJointWeight_integrable μ ν a ha b)
    (Filter.Eventually.of_forall (fun p => (gaussianMatrixWeight_pos a _ _ _).le))).symm

lemma flatSpectralMatrixWeight_eq_integral
    (ν : Measure (flatUnitDirections 𝕂 n L)) [IsProbabilityMeasure ν]
    (a : ℝ) (ha : 0 < a) (b : 𝕂) (x : Fin n → Fin n → 𝕂) :
    flatSpectralMatrixWeight ν a b x =
      ENNReal.ofReal (∫ v, flatSpectralJointWeight a b (v,x) ∂ν) := by
  have hc : Continuous (fun v : flatUnitDirections 𝕂 n L => flatSpectralJointWeight a b (v,x)) :=
    (flatSpectralJointWeight_continuous a b).comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun v : flatUnitDirections 𝕂 n L => flatSpectralJointWeight a b (v,x)) ν := by
    apply Integrable.of_bound hc.measurable.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro v
    dsimp only [flatSpectralJointWeight]
    rw [Real.norm_eq_abs,abs_of_nonneg (gaussianMatrixWeight_pos a _ _ _).le]
    exact gaussianMatrixWeight_le_one a ha _ _ _
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun v => (gaussianMatrixWeight_pos a _ _ _).le))).symm

#print axioms flatSpectralMatrixWeight_measurable
#print axioms flatSpectralMatrixWeight_le_one
#print axioms flatSpectralMatrixWeight_normalizer
#print axioms flatSpectralMatrixWeight_eq_integral
end SpectralRadiusUpperTail
