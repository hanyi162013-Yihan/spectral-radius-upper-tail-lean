import SpectralRadiusUpperTail.SelectedGaussianReplacement
import SpectralRadiusUpperTail.CoordinateMaskEnergy
import SpectralRadiusUpperTail.ComplexGaussianFiniteScore

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma mixed_gaussian_normalizer_convolution (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (I : Finset (Fin n)) (v : Fin n → ℂ) (a : ℝ) (ha : 0 < a) (t : ℂ) :
    (∫ z : Fin n → ℂ, Real.exp (-‖t-∑ j, v j*z j‖^2/a)
      ∂Measure.pi (mixedCoordinateLaw μ properComplexGaussian I)) =
      (a/(a+∑ j, ‖coordinateMask Iᶜ v j‖^2))*
        gaussianFiniteNormalizer μ (a+∑ j, ‖coordinateMask Iᶜ v j‖^2) (coordinateMask I v) t := by
  let f : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) :=
    fun p j => if j ∈ I then p.1 j else p.2 j
  have hf : Measurable f := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j ∈ I <;> simp only [f, hj, if_true, if_false] <;> fun_prop
  have hl := coordinate_selection_law μ properComplexGaussian n I
  change ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => properComplexGaussian))).map f =
      Measure.pi (mixedCoordinateLaw μ properComplexGaussian I) at hl
  have hG : Measurable (fun z : Fin n → ℂ => Real.exp (-‖t-∑ j, v j*z j‖^2/a)) := by fun_prop
  rw [← hl, integral_map hf.aemeasurable hG.aestronglyMeasurable]
  have hFi : Integrable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      Real.exp (-‖t-∑ j, v j*f p j‖^2/a))
      ((Measure.pi (fun _ => μ)).prod (Measure.pi (fun _ => properComplexGaussian))) := by
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      exact Real.measurable_exp.comp (by fun_prop)) 1
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ha.le))
  rw [integral_prod _ hFi]
  have hs (x y : Fin n → ℂ) : t-∑ j, v j*f (x,y) j =
      (t-∑ j, coordinateMask I v j*x j)-∑ j, coordinateMask Iᶜ v j*y j := by
    dsimp [f]
    rw [selected_sum_split]
    abel
  simp_rw [hs]
  change (∫ x : Fin n → ℂ, gaussianFiniteNormalizer properComplexGaussian a (coordinateMask Iᶜ v)
      (t-∑ j, coordinateMask I v j*x j) ∂Measure.pi (fun _ => μ)) = _
  simp_rw [properComplexGaussian_finite_normalizer a ha]
  rw [integral_const_mul]
  rfl

#print axioms mixed_gaussian_normalizer_convolution
end SpectralRadiusUpperTail
