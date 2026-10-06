import SpectralRadiusUpperTail.GaussianMatrixWeight
import SpectralRadiusUpperTail.ComplexSoftChernoff

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma complex_row_laplace_factor {n : ℕ} (v : Fin n → ℂ) (u : ℂ) (x : Fin n → ℂ) :
    Real.exp (2*(star u*∑ j, v j*x j).re) =
      ∏ j, Real.exp (2*(star (star (v j)*u)*x j).re) := by
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [star_mul, star_star]
  congr 3
  ring

lemma complex_sharp_row_mgf (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (n : ℕ) (v : Fin n → ℂ) (u : ℂ) :
    Integrable (fun x : Fin n → ℂ => Real.exp (2*(star u*∑ j, v j*x j).re))
      (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin n → ℂ, Real.exp (2*(star u*∑ j, v j*x j).re) ∂Measure.pi (fun _ => μ)) ≤
      Real.exp ((∑ j, ‖v j‖^2)*‖u‖^2) := by
  simp_rw [complex_row_laplace_factor]
  refine ⟨Integrable.fintype_prod (fun j => hint (star (v j)*u)), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun j x => Real.exp (2*(star (star (v j)*u)*x).re))]
  calc
    _ ≤ ∏ j, Real.exp (‖star (v j)*u‖^2) := Finset.prod_le_prod
      (fun j _ => integral_nonneg (fun _ => Real.exp_nonneg _)) (fun j _ => hmgf _)
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [norm_mul, norm_star, mul_pow, Finset.sum_mul]

lemma complex_sharp_row_soft (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (‖u‖^2))
    (n : ℕ) (v : Fin n → ℂ) (a : ℝ) (ha : 0 < a) (t : ℂ) :
    gaussianFiniteNormalizer μ a v t ≤ Real.exp (-‖t‖^2/(a+∑ j, ‖v j‖^2)) := by
  let f : (Fin n → ℂ) → ℂ := fun x => ∑ j, v j*x j
  have hf : Measurable f := by dsimp [f]; fun_prop
  let P := (Measure.pi (fun _ : Fin n => μ)).map f
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hi (u : ℂ) : Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) P := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    exact (complex_sharp_row_mgf μ hint hmgf n v u).1
  have hb (u : ℂ) : (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂P) ≤
      Real.exp ((∑ j, ‖v j‖^2)*‖u‖^2) := by
    rw [integral_map hf.aemeasurable (by fun_prop)]
    exact (complex_sharp_row_mgf μ hint hmgf n v u).2
  have hh := complex_soft_integral_le P a (∑ j, ‖v j‖^2) t ha
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hi hb
  rw [integral_map hf.aemeasurable (by fun_prop)] at hh
  exact hh

#print axioms complex_row_laplace_factor
#print axioms complex_sharp_row_mgf
#print axioms complex_sharp_row_soft
end SpectralRadiusUpperTail
