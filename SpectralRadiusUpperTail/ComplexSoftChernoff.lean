import SpectralRadiusUpperTail.SoftRow
import SpectralRadiusUpperTail.GaussianFiniteCalculus

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma complex_soft_integral_le (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (a s : ℝ) (t : ℂ) (ha : 0 < a) (hs : 0 ≤ s)
    (hint : ∀ u : ℂ, Integrable (fun x : ℂ => Real.exp (2*(star u*x).re)) μ)
    (hmgf : ∀ u : ℂ, (∫ x : ℂ, Real.exp (2*(star u*x).re) ∂μ) ≤ Real.exp (s*‖u‖^2)) :
    (∫ x : ℂ, Real.exp (-‖t-x‖^2/a) ∂μ) ≤ Real.exp (-‖t‖^2/(a+s)) := by
  let f : ℂ → ℝ × ℝ := fun z => (z.re, z.im)
  have hf : Measurable f := by fun_prop
  let P := μ.map f
  have hi (u v : ℝ) : Integrable (fun x : ℝ × ℝ => Real.exp (2*(u*x.1+v*x.2))) P := by
    apply (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr
    simpa [f, Complex.mul_re, Function.comp_def] using! hint (⟨u, v⟩ : ℂ)
  have hg (u v : ℝ) : (∫ x : ℝ × ℝ, Real.exp (2*(u*x.1+v*x.2)) ∂P) ≤
      Real.exp (s*(u^2+v^2)) := by
    rw [integral_map hf.aemeasurable (by fun_prop)]
    have hb := hmgf (⟨u, v⟩ : ℂ)
    rw [Complex.sq_norm] at hb
    simpa [f, Complex.mul_re, Complex.normSq_apply, pow_two] using hb
  have hh := planar_soft_integral_le P a s t.re t.im ha hs hi hg
  rw [integral_map hf.aemeasurable (by fun_prop)] at hh
  convert! hh using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      congr 2
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, f]
      ring)
  · congr 2
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring

#print axioms complex_soft_integral_le
end SpectralRadiusUpperTail
