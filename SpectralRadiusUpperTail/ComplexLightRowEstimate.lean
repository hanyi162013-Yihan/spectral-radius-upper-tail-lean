import SpectralRadiusUpperTail.MixedGaussianConvolution
import SpectralRadiusUpperTail.ComplexSharpRowMGF

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma complex_light_row_estimate (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℂ => x) 2 μ)
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hv : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hp : (∫ x : ℂ, x^2 ∂μ) = 0) (h3 : Integrable (fun x : ℂ => ‖x‖^3) μ)
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ I : Finset (Fin n), ∀ v : Fin n → ℂ,
      (∑ j, ‖v j‖^2) = 1 → ∀ d : ℝ, 0 ≤ d →
      (∀ j, j ∉ I → ‖v j‖ ≤ d) → ∀ t : ℂ,
      gaussianFiniteNormalizer μ a v t ≤
        (a/(a+Iᶜ.sum (fun j => ‖v j‖^2)))*Real.exp (-‖t‖^2/(a+1))+C*d := by
  let C := (gaussianThirdConstant a/2)*((∫ x : ℂ, ‖x‖^3 ∂μ)+(∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian))
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (gaussianThirdConstant_nonneg a ha) (by norm_num))
    (add_nonneg (integral_nonneg (fun _ => by positivity)) (integral_nonneg (fun _ => by positivity)))
  refine ⟨C, hC, ?_⟩
  intro n I v hve d hd hsmall t
  have hr := gaussian_selected_replacement μ properComplexGaussian hX properComplexGaussian_memLp
    (hm.trans properComplexGaussian_mean.symm) (hv.trans properComplexGaussian_energy.symm)
    (hp.trans properComplexGaussian_pseudo.symm) h3 properComplexGaussian_third_integrable a ha n I v t
  have hb := hr.trans (selected_cube_error_bound I v C d hC hd hve.le hsmall)
  rw [mixed_gaussian_normalizer_convolution μ n I v a ha t] at hb
  have hq : 0 ≤ ∑ j, ‖coordinateMask Iᶜ v j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := complex_sharp_row_soft μ hint hmgf n (coordinateMask I v)
    (a+∑ j, ‖coordinateMask Iᶜ v j‖^2) (by linarith) t
  have henergy : (a+∑ j, ‖coordinateMask Iᶜ v j‖^2)+(∑ j, ‖coordinateMask I v j‖^2) = a+1 := by
    have he := coordinateMask_compl_energy I v
    rw [hve] at he
    linarith
  rw [henergy] at hs
  have hden : 0 ≤ a+∑ j, ‖coordinateMask Iᶜ v j‖^2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hs (div_nonneg ha.le hden)
  have hab := le_abs_self (gaussianFiniteNormalizer μ a v t-
    (a/(a+∑ j, ‖coordinateMask Iᶜ v j‖^2))*
      gaussianFiniteNormalizer μ (a+∑ j, ‖coordinateMask Iᶜ v j‖^2) (coordinateMask I v) t)
  rw [coordinateMask_energy] at hb hmul hab
  linarith

#print axioms complex_light_row_estimate
end SpectralRadiusUpperTail
