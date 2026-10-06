import SpectralRadiusUpperTail.RCLikeCovariance
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

noncomputable def scalarPushforward (μ : Measure 𝕂) (v : 𝕂) : Measure 𝕂 :=
  μ.map (fun x => v*x)

instance scalarPushforward_probability (μ : Measure 𝕂) [IsProbabilityMeasure μ] (v : 𝕂) :
    IsProbabilityMeasure (scalarPushforward μ v) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma scalarPushforward_memLp (μ : Measure 𝕂) (v : 𝕂)
    (hX : MemLp (fun x : 𝕂 => x) 2 μ) :
    MemLp (fun x : 𝕂 => x) 2 (scalarPushforward μ v) := by
  apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
    (show AEMeasurable (fun x : 𝕂 => v*x) μ by fun_prop)).mpr
  exact hX.const_mul v

lemma scalarPushforward_mean (μ : Measure 𝕂) (v : 𝕂) :
    (∫ x : 𝕂, x ∂scalarPushforward μ v) = v*(∫ x : 𝕂, x ∂μ) := by
  rw [scalarPushforward, integral_map (f := fun x : 𝕂 => x) (by fun_prop) (by fun_prop),
    integral_const_mul]

lemma scalarPushforward_energy (μ : Measure 𝕂) (v : 𝕂) :
    (∫ x : 𝕂, ‖x‖^2 ∂scalarPushforward μ v) = ‖v‖^2*(∫ x : 𝕂, ‖x‖^2 ∂μ) := by
  rw [scalarPushforward, integral_map (f := fun x : 𝕂 => ‖x‖^2) (by fun_prop) (by fun_prop)]
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul]

lemma scalarPushforward_pseudovariance (μ : Measure 𝕂) (v : 𝕂) :
    (∫ x : 𝕂, x^2 ∂scalarPushforward μ v) = v^2*(∫ x : 𝕂, x^2 ∂μ) := by
  rw [scalarPushforward, integral_map (f := fun x : 𝕂 => x^2) (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

lemma scalarPushforward_thirdMoment (μ : Measure 𝕂) (v : 𝕂)
    (h3 : Integrable (fun x : 𝕂 => ‖x‖^3) μ) :
    Integrable (fun x : 𝕂 => ‖x‖^3) (scalarPushforward μ v) ∧
      (∫ x : 𝕂, ‖x‖^3 ∂scalarPushforward μ v) = ‖v‖^3*(∫ x : 𝕂, ‖x‖^3 ∂μ) := by
  constructor
  · apply (integrable_map_measure (g := fun x : 𝕂 => ‖x‖^3) (by fun_prop)
      (show AEMeasurable (fun x : 𝕂 => v*x) μ by fun_prop)).mpr
    simpa only [Function.comp_def, norm_mul, mul_pow] using h3.const_mul (‖v‖^3)
  · rw [scalarPushforward, integral_map (f := fun x : 𝕂 => ‖x‖^3) (by fun_prop) (by fun_prop)]
    simp_rw [norm_mul, mul_pow]
    rw [integral_const_mul]

#print axioms scalarPushforward_memLp
#print axioms scalarPushforward_thirdMoment
end SpectralRadiusUpperTail
