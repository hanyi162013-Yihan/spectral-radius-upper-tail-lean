import SpectralRadiusUpperTail.GaussianProductReplacement
import SpectralRadiusUpperTail.ComplexGaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Replacement by the actual unit-variance proper complex Gaussian, derived
from original entry assumptions without independence of real and imaginary parts. -/
theorem complex_gaussian_normalizer_replacement (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hm : (∫ x : ℂ, x ∂μ) = 0) (hvar : (∫ x : ℂ, ‖x‖^2 ∂μ) = 1)
    (hpseudo : (∫ x : ℂ, x^2 ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (he : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (v : Fin N → ℂ) (s : ℂ) :
    |(∫ x : Fin N → ℂ, Real.exp (-‖s-∑ i, v i*x i‖^2/a) ∂Measure.pi (fun _ => μ))-
      (∫ x : Fin N → ℂ, Real.exp (-‖s-∑ i, v i*x i‖^2/a)
        ∂Measure.pi (fun _ => properComplexGaussian))| ≤
      ((gaussianThirdConstant a/2)*((∫ x : ℂ, ‖x‖^3 ∂μ)+
        (∫ x : ℂ, ‖x‖^3 ∂properComplexGaussian)))*∑ i, ‖v i‖^3 := by
  have hX : MemLp (fun x : ℂ => x) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (squareExp_norm_pow_integrable μ τ hτ he 2)
  exact gaussian_product_replacement μ properComplexGaussian hX properComplexGaussian_memLp
    (hm.trans properComplexGaussian_mean.symm) (hvar.trans properComplexGaussian_energy.symm)
    (hpseudo.trans properComplexGaussian_pseudo.symm)
    (squareExp_norm_pow_integrable μ τ hτ he 3) properComplexGaussian_third_integrable a ha N v s

#print axioms complex_gaussian_normalizer_replacement
end SpectralRadiusUpperTail
