import SpectralRadiusUpperTail.GaussianTaylorBound
import SpectralRadiusUpperTail.Centering
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def gaussianTaylorPolynomial (a : ℝ) (s x : E) : ℝ :=
  Real.exp (-‖s‖^2/a)+((-2/a)*Real.exp (-‖s‖^2/a))*inner ℝ s x+
    (((-2/a)/2)*Real.exp (-‖s‖^2/a))*‖x‖^2+
    (((-2/a)^2/2)*Real.exp (-‖s‖^2/a))*(inner ℝ s x)^2

lemma gaussianTaylorPolynomial_remainder (a : ℝ) (ha : 0 < a) (s x : E) :
    |Real.exp (-‖s+x‖^2/a)-gaussianTaylorPolynomial a s x| ≤
      (gaussianThirdConstant a/2)*‖x‖^3 := by
  have he : gaussianTaylorPolynomial a s x =
      Real.exp (-‖s‖^2/a)+((-2/a)*inner ℝ s x)*Real.exp (-‖s‖^2/a)+
        (1/2)*(((-2/a)*‖x‖^2+((-2/a)*inner ℝ s x)^2)*Real.exp (-‖s‖^2/a)) := by
    unfold gaussianTaylorPolynomial
    ring
  rw [he]
  exact gaussian_quadratic_remainder a ha s x

lemma hilbert_projection_square_integrable (μ : Measure E)
    (hX : MemLp (fun x : E => x) 2 μ) (s : E) :
    Integrable (fun x : E => (inner ℝ s x)^2) μ := by
  have hi : MemLp (fun x : E => inner ℝ s x) 2 μ := hX.const_inner s
  convert! hi.integrable_mul hi using 1
  ext x
  simp [pow_two]

lemma gaussianTaylorPolynomial_integral (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (a : ℝ) (s : E) :
    Integrable (gaussianTaylorPolynomial a s) μ ∧
      (∫ x, gaussianTaylorPolynomial a s x ∂μ) =
        Real.exp (-‖s‖^2/a)+((-2/a)*Real.exp (-‖s‖^2/a))*(∫ x, inner ℝ s x ∂μ)+
        (((-2/a)/2)*Real.exp (-‖s‖^2/a))*(∫ x : E, ‖x‖^2 ∂μ)+
        (((-2/a)^2/2)*Real.exp (-‖s‖^2/a))*(∫ x, (inner ℝ s x)^2 ∂μ) := by
  have h1 := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h2 := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hi : Integrable (fun x : E => inner ℝ s x) μ := h1.const_inner s
  have hi2 := hilbert_projection_square_integrable μ hX s
  have hp := (((integrable_const (Real.exp (-‖s‖^2/a))).add
    (hi.const_mul ((-2/a)*Real.exp (-‖s‖^2/a)))).add
    (h2.const_mul (((-2/a)/2)*Real.exp (-‖s‖^2/a)))).add
    (hi2.const_mul (((-2/a)^2/2)*Real.exp (-‖s‖^2/a)))
  refine ⟨hp, ?_⟩
  unfold gaussianTaylorPolynomial
  rw [integral_add, integral_add, integral_add]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
  all_goals first | exact integrable_const _ | exact hi.const_mul _ | exact h2.const_mul _ |
    exact hi2.const_mul _ | exact (integrable_const _).add (hi.const_mul _) |
    exact ((integrable_const _).add (hi.const_mul _)).add (h2.const_mul _)

lemma gaussianShift_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (a : ℝ) (ha : 0 < a) (s : E) :
    Integrable (fun x => Real.exp (-‖s+x‖^2/a)) μ := by
  apply (integrable_const (1 : ℝ)).mono_nonneg (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
  apply Filter.Eventually.of_forall
  intro x
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _)) ha.le)

/-- Actual one-law replacement for a Gaussian soft test. Matching first and
second moments cancels the proved Taylor polynomial, leaving a cubic-moment error.
The two laws can be atomic and their real coordinates may be dependent. -/
theorem gaussian_integral_replacement (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : E => x) 2 μ) (hXν : MemLp (fun x : E => x) 2 ν)
    (hm : (∫ x : E, x ∂μ) = ∫ x : E, x ∂ν)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) = ∫ x : E, ‖x‖^2 ∂ν)
    (hcov : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = ∫ x : E, (inner ℝ s x)^2 ∂ν)
    (h3μ : Integrable (fun x : E => ‖x‖^3) μ)
    (h3ν : Integrable (fun x : E => ‖x‖^3) ν)
    (a : ℝ) (ha : 0 < a) (s : E) :
    |(∫ x : E, Real.exp (-‖s+x‖^2/a) ∂μ)-
      (∫ x : E, Real.exp (-‖s+x‖^2/a) ∂ν)| ≤
      (gaussianThirdConstant a/2)*((∫ x : E, ‖x‖^3 ∂μ)+(∫ x : E, ‖x‖^3 ∂ν)) := by
  obtain ⟨hPμ, heμ⟩ := gaussianTaylorPolynomial_integral μ hXμ a s
  obtain ⟨hPν, heν⟩ := gaussianTaylorPolynomial_integral ν hXν a s
  have h1μ := hXμ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h1ν := hXν.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hproj : (∫ x : E, inner ℝ s x ∂μ) = ∫ x : E, inner ℝ s x ∂ν := by
    rw [integral_inner h1μ, integral_inner h1ν, hm]
  have hPeq : (∫ x, gaussianTaylorPolynomial a s x ∂μ) =
      ∫ x, gaussianTaylorPolynomial a s x ∂ν := by
    rw [heμ, heν, hproj, hvar, hcov s]
  have hμerr : |(∫ x : E, Real.exp (-‖s+x‖^2/a) ∂μ)-
      (∫ x, gaussianTaylorPolynomial a s x ∂μ)| ≤
        (gaussianThirdConstant a/2)*(∫ x : E, ‖x‖^3 ∂μ) := by
    rw [← integral_sub (gaussianShift_integrable μ a ha s) hPμ]
    have hh := norm_integral_le_of_norm_le
      (f := fun x : E => Real.exp (-‖s+x‖^2/a)-gaussianTaylorPolynomial a s x)
      (h3μ.const_mul (gaussianThirdConstant a/2))
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using gaussianTaylorPolynomial_remainder a ha s x))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hh
  have hνerr : |(∫ x : E, Real.exp (-‖s+x‖^2/a) ∂ν)-
      (∫ x, gaussianTaylorPolynomial a s x ∂ν)| ≤
        (gaussianThirdConstant a/2)*(∫ x : E, ‖x‖^3 ∂ν) := by
    rw [← integral_sub (gaussianShift_integrable ν a ha s) hPν]
    have hh := norm_integral_le_of_norm_le
      (f := fun x : E => Real.exp (-‖s+x‖^2/a)-gaussianTaylorPolynomial a s x)
      (h3ν.const_mul (gaussianThirdConstant a/2))
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs] using gaussianTaylorPolynomial_remainder a ha s x))
    simpa only [Real.norm_eq_abs, integral_const_mul] using hh
  have ht := abs_sub_le (∫ x : E, Real.exp (-‖s+x‖^2/a) ∂μ)
    (∫ x, gaussianTaylorPolynomial a s x ∂μ) (∫ x : E, Real.exp (-‖s+x‖^2/a) ∂ν)
  rw [hPeq, abs_sub_comm (∫ x, gaussianTaylorPolynomial a s x ∂ν)] at ht
  rw [hPeq] at hμerr
  nlinarith only [ht, hμerr, hνerr]

#print axioms gaussian_integral_replacement
end SpectralRadiusUpperTail
