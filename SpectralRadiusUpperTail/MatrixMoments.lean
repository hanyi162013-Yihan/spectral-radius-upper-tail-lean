import SpectralRadiusUpperTail.MatrixPolynomial
import SpectralRadiusUpperTail.GaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {n : ℕ}

theorem frobeniusPowerSquared_integrable
    (μ : (Fin n × Fin n) → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hint : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (k : ℕ) :
    Integrable (frobeniusPowerSquared k) (Measure.pi μ) := by
  have heq : evalNatPolynomial (frobeniusPowerPolynomial n k) = frobeniusPowerSquared k :=
    funext (fun x => eval_frobeniusPowerPolynomial x k)
  rw [← heq]
  exact polynomial_product_integrable μ hint _

/-- A finite-dimensional matrix moment theorem, before choosing an entry law. -/
theorem matrix_power_moment_comparison
    (μ ν : (Fin n × Fin n) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hintμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i))
    (hintν : ∀ i k, Integrable (fun x : ℝ => x^k) (ν i))
    (hpos : ∀ i k, 0 ≤ ∫ x : ℝ, x^k ∂μ i)
    (hdom : ∀ i k, (∫ x : ℝ, x^k ∂μ i) ≤ ∫ x : ℝ, x^k ∂ν i) (k : ℕ) :
    (∫ x, frobeniusPowerSquared k x ∂Measure.pi μ) ≤
      ∫ x, frobeniusPowerSquared k x ∂Measure.pi ν := by
  have h := polynomial_expectation_comparison μ ν hintμ hintν hpos hdom
    (frobeniusPowerPolynomial n k)
  simpa only [eval_frobeniusPowerPolynomial] using h

noncomputable def signMatrixLaw (n : ℕ) : Measure ((Fin n × Fin n) → ℝ) :=
  Measure.pi (fun _ => signMeasure)
noncomputable def gaussianMatrixLaw (n : ℕ) : Measure ((Fin n × Fin n) → ℝ) :=
  Measure.pi (fun _ => standardNormal)

instance signMatrixLaw_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (signMatrixLaw n) := by
  unfold signMatrixLaw
  infer_instance
instance gaussianMatrixLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianMatrixLaw n) := by
  unfold gaussianMatrixLaw
  infer_instance

/-- Actual iid Bernoulli matrices are compared to actual iid standard Gaussian matrices. -/
theorem sign_matrix_power_moment_le_gaussian (n k : ℕ) :
    (∫ x, frobeniusPowerSquared k x ∂signMatrixLaw n) ≤
      ∫ x, frobeniusPowerSquared k x ∂gaussianMatrixLaw n :=
  matrix_power_moment_comparison (fun _ => signMeasure) (fun _ => standardNormal)
    (fun _ _ => sign_integrable _) (fun _ => standardNormal_pow_integrable)
    (fun _ => sign_moment_nonneg) (fun _ => sign_moment_le_standardNormal) k

def scaledFrobeniusPowerSquared (c : ℝ) (k : ℕ) (x : (Fin n × Fin n) → ℝ) : ℝ :=
  ∑ i, ∑ j, ((((c • entryMatrix x)^k) i j)^2)

lemma scaledFrobeniusPowerSquared_eq (c : ℝ) (k : ℕ) (x : (Fin n × Fin n) → ℝ) :
    scaledFrobeniusPowerSquared c k x = (c^k)^2 * frobeniusPowerSquared k x := by
  simp only [scaledFrobeniusPowerSquared, frobeniusPowerSquared, smul_pow,
    Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Includes the usual n^{-1/2} matrix normalization, for all finite n and k. -/
theorem normalized_sign_matrix_power_moment_le_gaussian (n k : ℕ) :
    (∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x ∂signMatrixLaw n) ≤
      ∫ x, scaledFrobeniusPowerSquared (1/Real.sqrt n) k x ∂gaussianMatrixLaw n := by
  simp_rw [scaledFrobeniusPowerSquared_eq, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (sign_matrix_power_moment_le_gaussian n k) (sq_nonneg _)

#print axioms matrix_power_moment_comparison
#print axioms sign_matrix_power_moment_le_gaussian
#print axioms normalized_sign_matrix_power_moment_le_gaussian
end SpectralRadiusUpperTail
