import SpectralRadiusUpperTail.GaussianDirectionalReplacement
import SpectralRadiusUpperTail.ScalarPushforwardMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

/-- Replacing a scalar entry in an actual Gaussian directional-derivative test costs a constant
 times the coefficient cubed and the two third absolute moments. Matching
 pseudovariances supplies the full real covariance condition. -/
theorem rclike_gaussianDirectional_scalar_replacement (μ ν : Measure 𝕂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : 𝕂 => x) 2 μ) (hXν : MemLp (fun x : 𝕂 => x) 2 ν)
    (hm : (∫ x : 𝕂, x ∂μ) = ∫ x : 𝕂, x ∂ν)
    (hvar : (∫ x : 𝕂, ‖x‖^2 ∂μ) = ∫ x : 𝕂, ‖x‖^2 ∂ν)
    (hpseudo : (∫ x : 𝕂, x^2 ∂μ) = ∫ x : 𝕂, x^2 ∂ν)
    (h3μ : Integrable (fun x : 𝕂 => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : 𝕂 => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (w s v : 𝕂) :
    |(∫ x : 𝕂, gaussianDirectional a w (s+v*x) ∂μ)-
      (∫ x : 𝕂, gaussianDirectional a w (s+v*x) ∂ν)| ≤
      (((gaussianDirectionalThirdConstant a/2)*‖w‖)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*‖v‖^3 := by
  have hm' : (∫ x : 𝕂, x ∂scalarPushforward μ v) = ∫ x : 𝕂, x ∂scalarPushforward ν v := by
    rw [scalarPushforward_mean, scalarPushforward_mean, hm]
  have hv' : (∫ x : 𝕂, ‖x‖^2 ∂scalarPushforward μ v) =
      ∫ x : 𝕂, ‖x‖^2 ∂scalarPushforward ν v := by
    rw [scalarPushforward_energy, scalarPushforward_energy, hvar]
  have hp' : (∫ x : 𝕂, x^2 ∂scalarPushforward μ v) = ∫ x : 𝕂, x^2 ∂scalarPushforward ν v := by
    rw [scalarPushforward_pseudovariance, scalarPushforward_pseudovariance, hpseudo]
  have hXμ' := scalarPushforward_memLp μ v hXμ
  have hXν' := scalarPushforward_memLp ν v hXν
  obtain ⟨h3μ', heμ⟩ := scalarPushforward_thirdMoment μ v h3μ
  obtain ⟨h3ν', heν⟩ := scalarPushforward_thirdMoment ν v h3ν
  have hh := gaussianDirectional_integral_replacement (scalarPushforward μ v) (scalarPushforward ν v)
    hXμ' hXν' hm' hv'
    (rclike_covariance_matching _ _ hXμ' hXν' hv' hp') h3μ' h3ν' a ha w s
  rw [heμ, heν] at hh
  simp only [scalarPushforward] at hh
  rw [integral_map (f := fun x : 𝕂 => gaussianDirectional a w (s+x)) (by fun_prop) (by unfold gaussianDirectional; fun_prop),
    integral_map (f := fun x : 𝕂 => gaussianDirectional a w (s+x)) (by fun_prop) (by unfold gaussianDirectional; fun_prop)] at hh
  have he : ((gaussianDirectionalThirdConstant a/2)*‖w‖)*
      (‖v‖^3*(∫ x : 𝕂, ‖x‖^3 ∂μ)+‖v‖^3*(∫ x : 𝕂, ‖x‖^3 ∂ν)) =
      (((gaussianDirectionalThirdConstant a/2)*‖w‖)*((∫ x : 𝕂, ‖x‖^3 ∂μ)+(∫ x : 𝕂, ‖x‖^3 ∂ν)))*‖v‖^3 := by ring
  rw [he] at hh
  exact hh

#print axioms rclike_gaussianDirectional_scalar_replacement
end SpectralRadiusUpperTail
