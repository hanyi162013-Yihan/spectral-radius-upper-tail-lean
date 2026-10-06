import SpectralRadiusUpperTail.MarkedRealStereoConeEnergy
import SpectralRadiusUpperTail.GaussianCoordinateIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

theorem markedRealProductGaussian_factor (m : ℕ) (x : ℝ × (Fin m → ℝ)) :
    ENNReal.ofReal (Real.exp (-markedRealProductEnergy m x)) =
      ENNReal.ofReal (Real.exp (-x.1^2)) *
        ENNReal.ofReal (Real.exp (-(∑ i, (x.2 i)^2))) := by
  rw [markedRealProductEnergy, neg_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem markedRealProductGaussian_halfspace (m : ℕ) :
    (∫⁻ x : ℝ × (Fin m → ℝ) in {y | 0 < y.1},
      ENNReal.ofReal (Real.exp (-markedRealProductEnergy m x))) =
        ENNReal.ofReal ((Real.sqrt Real.pi)^(m+1) / 2) := by
  have hs : {y : ℝ × (Fin m → ℝ) | 0 < y.1} = Set.Ioi 0 ×ˢ Set.univ := by
    ext y
    simp
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  simp_rw [markedRealProductGaussian_factor]
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r^2))) := by fun_prop
  have hg : Measurable (fun u : Fin m → ℝ =>
      ENNReal.ofReal (Real.exp (-(∑ i, (u i)^2)))) := by fun_prop
  rw [lintegral_prod_mul
    (f := fun r : ℝ => ENNReal.ofReal (Real.exp (-r^2)))
    (g := fun u : Fin m → ℝ => ENNReal.ofReal (Real.exp (-(∑ i, (u i)^2))))
    hf.aemeasurable hg.aemeasurable, gaussian_halfline_lintegral,
    gaussianCoordinateWeight_lintegral, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_succ]
  ring

#print axioms markedRealProductGaussian_factor
#print axioms markedRealProductGaussian_halfspace
end SpectralRadiusUpperTail
