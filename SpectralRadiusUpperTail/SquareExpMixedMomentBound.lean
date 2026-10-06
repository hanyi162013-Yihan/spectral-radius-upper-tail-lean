import SpectralRadiusUpperTail.IidMixedMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma mixedMoment_norm_le_absoluteMoment (μ : Measure 𝕂) (a b : ℕ) :
    ‖∫ z : 𝕂, z^a * (star z)^b ∂μ‖ ≤ ∫ z : 𝕂, ‖z‖^(a+b) ∂μ := by
  have h := norm_integral_le_integral_norm (f := fun z : 𝕂 => z^a * (star z)^b) (μ := μ)
  simpa only [norm_mul, norm_pow, norm_star, ← pow_add] using h

lemma mixedMoment_degree_two_norm_le (μ : Measure 𝕂)
    (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1) (a b : ℕ) (hab : a+b=2) :
    ‖∫ z : 𝕂, z^a * (star z)^b ∂μ‖ ≤ 1 := by
  have h := mixedMoment_norm_le_absoluteMoment μ a b
  simpa only [hab,hv] using h

lemma squareExp_mixedMoment_norm_le (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (a b : ℕ) :
    ‖∫ z : 𝕂, z^a * (star z)^b ∂μ‖ ≤
      (1+((a+b).factorial : ℝ)*(1/c)^(a+b)) *
        ∫ z : 𝕂, Real.exp (c*‖z‖^2) ∂μ := by
  apply (mixedMoment_norm_le_absoluteMoment μ a b).trans
  rw [← integral_const_mul]
  exact integral_mono (squareExp_norm_pow_integrable μ c hc hexp (a+b))
    (hexp.const_mul _) (fun z => norm_pow_squareExp_bound c ‖z‖ hc (a+b))

#print axioms mixedMoment_norm_le_absoluteMoment
#print axioms mixedMoment_degree_two_norm_le
#print axioms squareExp_mixedMoment_norm_le
end SpectralRadiusUpperTail
