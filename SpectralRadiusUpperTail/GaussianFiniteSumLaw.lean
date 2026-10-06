import SpectralRadiusUpperTail.RealGaussianReplacement
import SpectralRadiusUpperTail.ComplexGaussianMoments
import SpectralRadiusUpperTail.RowNormalizerBound
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Analysis.Normed.Operator.Mul

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

lemma scalarPushforward_isGaussian (μ : Measure 𝕂) [IsGaussian μ] (v : 𝕂) :
    IsGaussian (scalarPushforward μ v) := by
  convert! (show IsGaussian (μ.map (ContinuousLinearMap.mul ℝ 𝕂 v)) from inferInstance) using 1

instance properComplexGaussian_isGaussian : IsGaussian properComplexGaussian :=
  scalarPushforward_isGaussian _ _

instance standardNormal_isGaussian : IsGaussian standardNormal := by
  change IsGaussian (gaussianReal 0 1)
  infer_instance

/-- Actual independent Gaussian entries remain Gaussian after a finite weighted sum,
with complex coefficients interpreted as real continuous linear maps. -/
lemma gaussianFinite_sum_hasGaussianLaw (μ : Measure 𝕂) [IsGaussian μ]
    (N : ℕ) (v : Fin N → 𝕂) :
    HasGaussianLaw (fun x : Fin N → 𝕂 => ∑ i, v i*x i) (Measure.pi (fun _ => μ)) := by
  have hcoord (i : Fin N) : HasGaussianLaw (fun x : Fin N → 𝕂 => v i*x i)
      (Measure.pi (fun _ => μ)) := by
    have hh := ((measurePreserving_eval (fun _ : Fin N => μ) i).hasLaw).hasGaussianLaw
    convert! hh.map_fun (ContinuousLinearMap.mul ℝ 𝕂 (v i)) using 1
  have hind : iIndepFun (fun i (x : Fin N → 𝕂) => v i*x i) (Measure.pi (fun _ => μ)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  exact hind.hasGaussianLaw_fun_sum hcoord

/-- The actual real weighted Gaussian sum has the calculated variance, including
an empty coefficient family or zero total variance. -/
theorem realGaussian_finite_sum_law (N : ℕ) (v : Fin N → ℝ) :
    (Measure.pi (fun _ : Fin N => standardNormal)).map (fun x => ∑ i, v i*x i) =
      gaussianReal 0 (∑ i, ‖v i‖^2).toNNReal := by
  have hG : MemLp (fun x : ℝ => x) 2 standardNormal := by
    convert! (memLp_id_gaussianReal' (μ := 0) (v := 1) (2 : ℝ≥0∞) (by norm_num)) using 1
  have hm : (∫ x : ℝ, x ∂standardNormal) = 0 := by simpa using standardNormal_odd_moment 0
  have hv : (∫ x : ℝ, ‖x‖^2 ∂standardNormal) = 1 := by
    simpa only [Real.norm_eq_abs, sq_abs] using standardNormal_second_moment
  have hmean := iid_linear_row_mean standardNormal v hG hm
  have henergy := iid_linear_row_energy standardNormal v hG hm hv
  have hvariance : variance (fun x : Fin N → ℝ => ∑ i, v i*x i)
      (Measure.pi (fun _ => standardNormal)) = ∑ i, ‖v i‖^2 := by
    rw [variance_eq_integral
      (measurable_finite_sum _ (fun _ => by fun_prop)).aemeasurable, hmean]
    simpa only [sub_zero, Real.norm_eq_abs, sq_abs] using henergy
  have hLaw := HasGaussianLaw.map_eq_gaussianReal
    (gaussianFinite_sum_hasGaussianLaw standardNormal N v)
  rw [hmean, hvariance] at hLaw
  exact hLaw

#print axioms properComplexGaussian_isGaussian
#print axioms gaussianFinite_sum_hasGaussianLaw
#print axioms realGaussian_finite_sum_law
end SpectralRadiusUpperTail
