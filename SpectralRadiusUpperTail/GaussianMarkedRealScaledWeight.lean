import SpectralRadiusUpperTail.GaussianMarkedRealUnscaledWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem markedRealGaussianCharpolyMoment_measurable (m : ℕ) :
    Measurable (markedRealGaussianCharpolyMoment m) := by
  change Measurable (fun x => markedRealGaussianCharpolyMoment m x)
  simp_rw [markedRealGaussianCharpolyMoment_eq_ofReal_integral]
  exact (measurable_gaussian_charpoly_abs_parameter m).stronglyMeasurable.integral_prod_right'.measurable.ennreal_ofReal

theorem gaussianMarkedRealUnscaledWeight_measurable (m : ℕ) :
    Measurable (gaussianMarkedRealUnscaledWeight m) := by
  unfold gaussianMarkedRealUnscaledWeight
  have he : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-x^2/2))) := by fun_prop
  exact (measurable_const.mul he).mul
    (markedRealGaussianCharpolyMoment_measurable m)

/-- Scaled real one-point weight, defined on the full real line without
the radial-power quotient in the exterior density notation. -/
noncomputable def gaussianMarkedRealScaledWeight (m : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt ((m+1 : ℕ) : ℝ)) *
    gaussianMarkedRealUnscaledWeight m (Real.sqrt ((m+1 : ℕ) : ℝ)*r)

theorem gaussianMarkedRealScaledWeight_measurable (m : ℕ) :
    Measurable (gaussianMarkedRealScaledWeight m) :=
  measurable_const.mul ((gaussianMarkedRealUnscaledWeight_measurable m).comp (by fun_prop))

theorem gaussianMarkedRealScaledWeight_eq_exterior_density
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    gaussianMarkedRealScaledWeight m r = ENNReal.ofReal (gaussianMarkedRealDensity (m+1) r) :=
  gaussianMarkedRealUnscaledWeight_rescale m r hr

#print axioms markedRealGaussianCharpolyMoment_measurable
#print axioms gaussianMarkedRealUnscaledWeight_measurable
#print axioms gaussianMarkedRealScaledWeight_measurable
#print axioms gaussianMarkedRealScaledWeight_eq_exterior_density
end SpectralRadiusUpperTail
