import SpectralRadiusUpperTail.IndependentRows

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

lemma rowMap_measurable (a b : ι → ℝ) :
    Measurable (fun x : ι → ℝ × ℝ => (rowRe a b x, rowIm a b x)) := by
  unfold rowRe rowIm
  fun_prop

theorem independent_row_soft_integral_le
    (μ : ι → Measure (ℝ × ℝ)) [∀ j, SigmaFinite (μ j)] (a b : ι → ℝ)
    (hint : ∀ j u v, Integrable (fun x : ℝ × ℝ => Real.exp (2*(u*x.1+v*x.2))) (μ j))
    (hmgf : ∀ j u v, (∫ x : ℝ × ℝ, Real.exp (2*(u*x.1+v*x.2)) ∂μ j)
      ≤ Real.exp (u^2+v^2)) (c t q : ℝ) (hc : 0 < c) :
    (∫ x, Real.exp (-((rowRe a b x-t)^2+(rowIm a b x-q)^2)/c) ∂Measure.pi μ)
      ≤ Real.exp (-(t^2+q^2)/(c+coefficientMass a b)) := by
  let f : (ι → ℝ × ℝ) → ℝ × ℝ := fun x => (rowRe a b x, rowIm a b x)
  let ν := (Measure.pi μ).map f
  have hf : Measurable f := rowMap_measurable a b
  have hi (u v : ℝ) : Integrable (fun y : ℝ × ℝ => Real.exp (2*(u*y.1+v*y.2))) ν := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).2
    exact row_laplace_integrable μ a b hint u v
  have hg (u v : ℝ) : (∫ y : ℝ × ℝ, Real.exp (2*(u*y.1+v*y.2)) ∂ν)
      ≤ Real.exp (coefficientMass a b*(u^2+v^2)) := by
    rw [integral_map hf.aemeasurable (by fun_prop)]
    exact row_laplace_le μ a b hmgf u v
  have hs : 0 ≤ coefficientMass a b :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg (a j)) (sq_nonneg (b j)))
  have h := planar_soft_integral_le ν c (coefficientMass a b) t q hc hs hi hg
  rw [integral_map hf.aemeasurable (by fun_prop)] at h
  exact h

/-- A soft-row estimate for any finite row of independent actual four-point entries. -/
theorem fourPoint_product_soft_integral_le (a b : ι → ℝ) (c t q : ℝ) (hc : 0 < c) :
    (∫ x, Real.exp (-((rowRe a b x-t)^2+(rowIm a b x-q)^2)/c)
      ∂Measure.pi (fun _ : ι => fourPointMeasure))
      ≤ Real.exp (-(t^2+q^2)/(c+coefficientMass a b)) := by
  exact independent_row_soft_integral_le (fun _ => fourPointMeasure) a b
    (fun _ _ _ => fourPoint_integrable _) (fun _ => fourPoint_laplace) c t q hc

#print axioms independent_row_soft_integral_le
#print axioms fourPoint_product_soft_integral_le
end SpectralRadiusUpperTail
