import SpectralRadiusUpperTail.ExponentialFirstMoment
import SpectralRadiusUpperTail.PiRealDensity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

lemma exponential_pdf_integrable (r : ℝ) (hr : 0 < r) :
    Integrable (exponentialPDFReal r) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_exponentialPDFReal r).aestronglyMeasurable
    (Filter.Eventually.of_forall (exponentialPDFReal_nonneg hr))).mp
  change (∫⁻ x, exponentialPDF r x) ≠ ∞
  rw [lintegral_exponentialPDF_eq_one hr]
  exact ENNReal.one_ne_top

lemma exponential_product_density (m : ℕ) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i) :
    Measure.pi (fun i => expMeasure (r i)) =
      (volume : Measure (Fin m → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, exponentialPDFReal (r i) (x i))) := by
  rw [volume_pi,pi_withDensity_ofReal _ _
    (fun i => exponential_pdf_integrable (r i) (hr i))
    (fun i x => exponentialPDFReal_nonneg (hr i) x)]
  rfl

lemma exponential_product_density_nonneg (m : ℕ) (r x : Fin m → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∏ i, exponentialPDFReal (r i) (x i) =
      (∏ i, r i)*Real.exp (-(∑ i, r i*x i)) := by
  have he (i : Fin m) : exponentialPDFReal (r i) (x i) =
      r i * Real.exp (-(r i*x i)) := by
    unfold exponentialPDFReal gammaPDFReal
    simp [hx i]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.sum_neg_distrib]

#print axioms exponential_pdf_integrable
#print axioms exponential_product_density
#print axioms exponential_product_density_nonneg
end SpectralRadiusUpperTail
