import SpectralRadiusUpperTail.GaussianDirectionalBounds
import SpectralRadiusUpperTail.HilbertCovariance

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def gaussianDirectionalPolynomial (a : ℝ) (w s x : E) : ℝ :=
  ((-2/a)*inner ℝ s w*Real.exp (-‖s‖^2/a))+
  ((-2/a)*Real.exp (-‖s‖^2/a))*inner ℝ w x+
  ((-2/a)^2*inner ℝ s w*Real.exp (-‖s‖^2/a))*inner ℝ s x+
  (((-2/a)^2/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))*‖x‖^2+
  (((-2/a)^3/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))*(inner ℝ s x)^2+
  ((-2/a)^2*Real.exp (-‖s‖^2/a))*(inner ℝ s x*inner ℝ w x)

lemma gaussianDirectionalPolynomial_remainder (a : ℝ) (ha : 0 < a) (w s x : E) :
    |gaussianDirectional a w (s+x)-gaussianDirectionalPolynomial a w s x| ≤
      (gaussianDirectionalThirdConstant a/2)*‖w‖*‖x‖^3 := by
  have he : gaussianDirectionalPolynomial a w s x =
      gaussianDirectional a w s+gaussianDirectionalLineFirst a w s x 0+
        (1/2)*gaussianDirectionalLineSecond a w s x 0 := by
    dsimp [gaussianDirectionalPolynomial, gaussianDirectional, gaussianDirectionalLineFirst,
      gaussianDirectionalLineSecond, gaussianLineFirst, gaussianLineSecond,
      gaussianLine, gaussianLineSlope]
    simp only [zero_smul, add_zero, real_inner_comm x w]
    ring
  rw [he]
  exact gaussianDirectional_quadratic_remainder a ha w s x

lemma gaussianDirectionalPolynomial_integral (μ : Measure E) [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : E => x) 2 μ) (a : ℝ) (w s : E) :
    Integrable (gaussianDirectionalPolynomial a w s) μ ∧
      (∫ x, gaussianDirectionalPolynomial a w s x ∂μ) =
      ((-2/a)*inner ℝ s w*Real.exp (-‖s‖^2/a))+
      ((-2/a)*Real.exp (-‖s‖^2/a))*(∫ x, inner ℝ w x ∂μ)+
      ((-2/a)^2*inner ℝ s w*Real.exp (-‖s‖^2/a))*(∫ x, inner ℝ s x ∂μ)+
      (((-2/a)^2/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))*(∫ x : E, ‖x‖^2 ∂μ)+
      (((-2/a)^3/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))*(∫ x, (inner ℝ s x)^2 ∂μ)+
      ((-2/a)^2*Real.exp (-‖s‖^2/a))*(∫ x, inner ℝ s x*inner ℝ w x ∂μ) := by
  have hL1 := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hw : Integrable (fun x : E => inner ℝ w x) μ := hL1.const_inner w
  have hs : Integrable (fun x : E => inner ℝ s x) μ := hL1.const_inner s
  have hv := (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX
  have hss := hilbert_projection_square_integrable μ hX s
  have hsw := hilbert_projection_product_integrable μ hX s w
  have h0 := integrable_const ((-2/a)*inner ℝ s w*Real.exp (-‖s‖^2/a)) (μ := μ)
  have h1 := hw.const_mul ((-2/a)*Real.exp (-‖s‖^2/a))
  have h2 := hs.const_mul ((-2/a)^2*inner ℝ s w*Real.exp (-‖s‖^2/a))
  have h3 := hv.const_mul (((-2/a)^2/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))
  have h4 := hss.const_mul (((-2/a)^3/2)*inner ℝ s w*Real.exp (-‖s‖^2/a))
  have h5 := hsw.const_mul ((-2/a)^2*Real.exp (-‖s‖^2/a))
  refine ⟨(((((h0.add h1).add h2).add h3).add h4).add h5), ?_⟩
  unfold gaussianDirectionalPolynomial
  rw [integral_add, integral_add, integral_add, integral_add, integral_add]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
  all_goals first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 |
    exact h0.add h1 | exact (h0.add h1).add h2 | exact ((h0.add h1).add h2).add h3 |
    exact (((h0.add h1).add h2).add h3).add h4

/-- All constant, linear and mixed quadratic terms cancel under actual mean and
covariance matching. No coordinate-independence hypothesis is used. -/
lemma gaussianDirectionalPolynomial_integral_matching (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hXμ : MemLp (fun x : E => x) 2 μ) (hXν : MemLp (fun x : E => x) 2 ν)
    (hm : (∫ x : E, x ∂μ) = ∫ x : E, x ∂ν)
    (hvar : (∫ x : E, ‖x‖^2 ∂μ) = ∫ x : E, ‖x‖^2 ∂ν)
    (hcov : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = ∫ x : E, (inner ℝ s x)^2 ∂ν)
    (a : ℝ) (w s : E) :
    (∫ x, gaussianDirectionalPolynomial a w s x ∂μ) =
      ∫ x, gaussianDirectionalPolynomial a w s x ∂ν := by
  have h1μ := hXμ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h1ν := hXν.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hproj (u : E) : (∫ x : E, inner ℝ u x ∂μ) = ∫ x : E, inner ℝ u x ∂ν := by
    rw [integral_inner h1μ, integral_inner h1ν, hm]
  rw [(gaussianDirectionalPolynomial_integral μ hXμ a w s).2,
    (gaussianDirectionalPolynomial_integral ν hXν a w s).2,
    hproj w, hproj s, hvar, hcov s, hilbert_projection_product_matching μ ν hXμ hXν hcov s w]

#print axioms gaussianDirectionalPolynomial_remainder
#print axioms gaussianDirectionalPolynomial_integral_matching
end SpectralRadiusUpperTail
