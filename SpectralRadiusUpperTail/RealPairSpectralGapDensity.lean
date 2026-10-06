import SpectralRadiusUpperTail.RealPairSpectralGapMeasure

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def realPairSpectralGapBase : Measure (ℝ × (ℝ × ℝ)) :=
  (volume : Measure ℝ).prod (volume.restrict realSchurPairCoordinateDomain)

noncomputable def realPairSpectralGapDensity (n : ℝ) (v : ℝ × (ℝ × ℝ)) : ℝ :=
  (2*Real.pi)*Real.exp (-n*(v.1^2+v.2.1))*
    ((Real.sqrt (v.2.2+4*v.2.1))⁻¹*Real.exp (-(n/2)*v.2.2))

theorem realPairSpectralGapDensity_measurable (n : ℝ) :
    Measurable (realPairSpectralGapDensity n) := by
  unfold realPairSpectralGapDensity
  fun_prop

theorem realPairSpectralGapDensity_nonneg (n : ℝ) (v : ℝ × (ℝ × ℝ)) :
    0 ≤ realPairSpectralGapDensity n v := by
  unfold realPairSpectralGapDensity
  positivity

/-- An explicit density, as a measure identity, for the actual pair
coordinates. Both skew orientations have already been included. -/
theorem realPairSpectralGapMeasure_eq_density (n : ℝ) :
    realPairSpectralGapMeasure n=realPairSpectralGapBase.withDensity
      (fun v => ENNReal.ofReal (realPairSpectralGapDensity n v)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [realPairSpectralGapMeasure_lintegral n F hF,
    lintegral_withDensity_eq_lintegral_mul _
      (realPairSpectralGapDensity_measurable n).ennreal_ofReal hF]
  change _ = ∫⁻ v, ENNReal.ofReal (realPairSpectralGapDensity n v)*F v
    ∂(volume : Measure ℝ).prod (volume.restrict realSchurPairCoordinateDomain)
  rw [lintegral_prod (fun v => ENNReal.ofReal (realPairSpectralGapDensity n v)*F v)
    ((realPairSpectralGapDensity_measurable n).ennreal_ofReal.mul hF).aemeasurable]
  have he (x : ℝ) (v : ℝ × ℝ) :
      ENNReal.ofReal (realPairSpectralGapDensity n (x,v))*F (x,v) =
        ENNReal.ofReal (2*Real.pi)*
          (ENNReal.ofReal (Real.exp (-n*(x^2+v.1)))*
            (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹)*
              ENNReal.ofReal (Real.exp (-(n/2)*v.2))*F (x,v))) := by
    unfold realPairSpectralGapDensity
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    ac_rfl
  simp_rw [he,lintegral_const_mul' (ENNReal.ofReal (2*Real.pi)) _ ENNReal.ofReal_ne_top]

#print axioms realPairSpectralGapDensity_measurable
#print axioms realPairSpectralGapDensity_nonneg
#print axioms realPairSpectralGapMeasure_eq_density
end SpectralRadiusUpperTail
