import SpectralRadiusUpperTail.ExponentialWitnessFirstCoordinate
import SpectralRadiusUpperTail.ExponentialWitnessDensityBound
import SpectralRadiusUpperTail.ScaledExponentialSimplexIntegral
import Mathlib.MeasureTheory.Measure.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_witness_outer_integral (m : ℕ) (N u h₀ : ℝ) (h r : Fin m → ℝ)
    (hN : 0 < N) (hm : (m : ℝ) ≤ N) (hu : 0 < u) (hmin : ∀ i, h₀ ≤ h i)
    (hr : ∀ i, 1 ≤ r i) (hdom : ∀ i, (h i-h₀)/(2*u) ≤ r i) :
    ENNReal.ofReal ((1/2 : ℝ)^m*Real.exp (-N*h₀/u-N)) *
        ((1/2 : ℝ≥0∞)*ENNReal.ofReal (∏ i, (r i)⁻¹)) ≤
      ∫⁻ y : Fin m → ℝ, ∫⁻ y₀ : ℝ, exponentialWitnessIntegrand N u h₀ h y₀ y
        ∂expMeasure (1/2) ∂Measure.pi (fun _ => expMeasure (1/2)) := by
  letI : IsProbabilityMeasure (expMeasure (1/2)) := isProbabilityMeasure_expMeasure (by norm_num)
  let I : (Fin m → ℝ) → ℝ≥0∞ := fun y =>
    ∫⁻ y₀ : ℝ, exponentialWitnessIntegrand N u h₀ h y₀ y ∂expMeasure (1/2)
  have hI : Measurable I := (exponentialWitnessIntegrand_measurable m N u h₀ h).lintegral_prod_left'
  let C := ENNReal.ofReal ((1/2 : ℝ)^m*Real.exp (-N*h₀/u-N))
  let D : (Fin m → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (∏ i, exponentialPDFReal (1/2) (y i))
  have hD : Measurable D := by dsimp [D]; fun_prop
  change C*((1/2 : ℝ≥0∞)*ENNReal.ofReal (∏ i, (r i)⁻¹)) ≤ ∫⁻ y, I y ∂Measure.pi (fun _ => expMeasure (1/2))
  rw [exponential_product_density m (fun _ => 1/2) (fun _ => by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ hD hI]
  have hbase := mul_le_mul' (le_refl C) (scaled_simplex_exponential_lintegral_lower m N hN hm r hr)
  apply hbase.trans
  rw [← lintegral_const_mul C (show Measurable
    (fun y : Fin m → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, r i*y i)))) by fun_prop)]
  apply (show (∫⁻ y in positiveSimplexAt m (2*N), C*ENNReal.ofReal (Real.exp (-(∑ i, r i*y i)))) ≤
      ∫⁻ y in positiveSimplexAt m (2*N), D y*I y from ?_).trans
    (setLIntegral_le_lintegral _ _)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (positiveSimplexAt_measurable m (2*N))] with y hy
  have hpd : 0 ≤ ∏ i, exponentialPDFReal (1/2) (y i) :=
    Finset.prod_nonneg (fun i _ => exponentialPDFReal_nonneg (by norm_num) _)
  calc
    C*ENNReal.ofReal (Real.exp (-(∑ i, r i*y i))) =
        ENNReal.ofReal (((1/2 : ℝ)^m*Real.exp (-N*h₀/u-N))*Real.exp (-(∑ i, r i*y i))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((∏ i, exponentialPDFReal (1/2) (y i))*
        (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u)))*
        Real.exp (-(1/2 : ℝ)*(2*N-∑ i, y i))) :=
      ENNReal.ofReal_le_ofReal (exponential_witness_density_lower N u h₀ h y r hu hy.1 hdom)
    _ = D y*(ENNReal.ofReal (Real.exp (-N*h₀/u)*Real.exp (-(∑ i, (h i-h₀)*y i)/(2*u)))*
        ENNReal.ofReal (Real.exp (-(1/2 : ℝ)*(2*N-∑ i, y i)))) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hpd (by positivity)), ENNReal.ofReal_mul hpd, mul_assoc]
    _ ≤ D y*I y := mul_le_mul' le_rfl (exponential_witness_first_coordinate N u h₀ h y hN hu hy.1 hmin hy.2)

#print axioms exponential_witness_outer_integral
end SpectralRadiusUpperTail
