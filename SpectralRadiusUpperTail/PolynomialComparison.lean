import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ : Type*} [Fintype σ]

noncomputable def evalNatPolynomial (p : MvPolynomial σ ℕ) (x : σ → ℝ) : ℝ :=
  p.eval₂ (Nat.castRingHom ℝ) x

lemma evalNatPolynomial_expansion (p : MvPolynomial σ ℕ) (x : σ → ℝ) :
    evalNatPolynomial p x = ∑ d ∈ p.support, ((p.coeff d : ℕ) : ℝ)*(∏ i, x i^(d i)) := by
  exact MvPolynomial.eval₂_eq' (Nat.castRingHom ℝ) x p

theorem monomial_product_integrable (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hint : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (d : σ →₀ ℕ) :
    Integrable (fun x : σ → ℝ => ∏ i, x i^(d i)) (Measure.pi μ) :=
  Integrable.fintype_prod (fun i => hint i (d i))

theorem polynomial_product_integrable (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hint : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (p : MvPolynomial σ ℕ) :
    Integrable (evalNatPolynomial p) (Measure.pi μ) := by
  classical
  simp_rw [show evalNatPolynomial p = fun x =>
    ∑ d ∈ p.support, ((p.coeff d : ℕ) : ℝ)*(∏ i, x i^(d i)) from
      funext (evalNatPolynomial_expansion p)]
  exact integrable_finsetSum _ (fun d _ => (monomial_product_integrable μ hint d).const_mul _)

theorem integral_polynomial_product (μ : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hint : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (p : MvPolynomial σ ℕ) :
    (∫ x, evalNatPolynomial p x ∂Measure.pi μ) =
      ∑ d ∈ p.support, ((p.coeff d : ℕ) : ℝ)*(∏ i, ∫ x : ℝ, x^(d i) ∂μ i) := by
  classical
  simp_rw [evalNatPolynomial_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d _
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (fun i (x : ℝ) => x^(d i))]
  · exact fun d _ => (monomial_product_integrable μ hint d).const_mul _

/-- Coefficient positivity and actual product integration yield moment comparison. -/
theorem polynomial_expectation_comparison
    (μ ν : σ → Measure ℝ) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hintμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i))
    (hintν : ∀ i k, Integrable (fun x : ℝ => x^k) (ν i))
    (hpos : ∀ i k, 0 ≤ ∫ x : ℝ, x^k ∂μ i)
    (hdom : ∀ i k, (∫ x : ℝ, x^k ∂μ i) ≤ ∫ x : ℝ, x^k ∂ν i)
    (p : MvPolynomial σ ℕ) :
    (∫ x, evalNatPolynomial p x ∂Measure.pi μ) ≤
      ∫ x, evalNatPolynomial p x ∂Measure.pi ν := by
  rw [integral_polynomial_product μ hintμ, integral_polynomial_product ν hintν]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.prod_le_prod (fun i _ => hpos i (d i)) (fun i _ => hdom i (d i))

#print axioms polynomial_product_integrable
#print axioms integral_polynomial_product
#print axioms polynomial_expectation_comparison
end SpectralRadiusUpperTail
