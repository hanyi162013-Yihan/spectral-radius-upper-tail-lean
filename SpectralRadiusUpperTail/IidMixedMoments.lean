import SpectralRadiusUpperTail.SquareExpPolynomialMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ComplexConjugate
variable {𝕂 ι : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] [Fintype ι]

lemma squareExp_mixedPower_integrable (μ : Measure 𝕂) (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ) (a b : ℕ) :
    Integrable (fun x : 𝕂 => x^a*(star x)^b) μ := by
  have h := squareExp_norm_pow_integrable μ c hc hexp (a+b)
  apply h.mono' (by fun_prop)
  filter_upwards [] with x
  simp only [norm_mul, norm_pow, norm_star, pow_add]
  exact le_rfl

lemma iidMixedProduct_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ)
    (a b : ι → ℕ) :
    Integrable (fun x : ι → 𝕂 => ∏ i, (x i)^(a i)*(star (x i))^(b i))
      (Measure.pi (fun _ : ι => μ)) :=
  Integrable.fintype_prod (fun i => squareExp_mixedPower_integrable μ c hc hexp (a i) (b i))

lemma iidMixedProduct_expectation (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (a b : ι → ℕ) :
    (∫ x : ι → 𝕂, ∏ i, (x i)^(a i)*(star (x i))^(b i) ∂Measure.pi (fun _ : ι => μ)) =
      ∏ i, ∫ z : 𝕂, z^(a i)*(star z)^(b i) ∂μ :=
  integral_fintype_prod_eq_prod (fun i (z : 𝕂) => z^(a i)*(star z)^(b i))

/-- A single occurrence of a centered iid entry, conjugated or not, annihilates
an entire mixed path-product expectation. -/
lemma iidMixedProduct_singleton_zero (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (a b : ι → ℕ) (i : ι) (hi : a i+b i = 1) :
    (∫ x : ι → 𝕂, ∏ j, (x j)^(a j)*(star (x j))^(b j) ∂Measure.pi (fun _ : ι => μ)) = 0 := by
  classical
  rw [iidMixedProduct_expectation]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases ha : a i = 0
  · have hb : b i = 1 := by omega
    simp only [ha, hb, pow_zero, pow_one, one_mul]
    change (∫ x : 𝕂, conj x ∂μ) = 0
    rw [integral_conj, hm, map_zero]
  · have ha' : a i = 1 := by omega
    have hb : b i = 0 := by omega
    simpa only [ha', hb, pow_one, pow_zero, mul_one] using hm

#print axioms squareExp_mixedPower_integrable
#print axioms iidMixedProduct_integrable
#print axioms iidMixedProduct_expectation
#print axioms iidMixedProduct_singleton_zero
end SpectralRadiusUpperTail
