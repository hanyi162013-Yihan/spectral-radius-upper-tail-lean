import SpectralRadiusUpperTail.RealPairSpectralGapIntegral
import SpectralRadiusUpperTail.RealPairGaussianGapDisintegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The gap has been integrated out, leaving the real part and the
squared imaginary part of the selected conjugate pair. -/
theorem realPairGaussian_spectral_marginal
    (n : ℝ) (hn : 0 < n) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ B in realPairNonrealEntrySet, realPairGaussianWeight n B*
      H (realPairCenter (Matrix.of B.curry),realPairHeightSq (Matrix.of B.curry))) =
      ENNReal.ofReal (2*Real.pi)*
        ∫⁻ x : ℝ, ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-n*(x^2+u)))*
            (((ENNReal.ofReal (n/2))⁻¹*schurGapKernelNormalizer n (Real.sqrt u))*H (x,u)) := by
  have hF : Measurable (fun v : ℝ × (ℝ × ℝ) => H (v.1,v.2.1)) :=
    hH.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have he := realPairGaussian_spectralGap_lintegral n
    (fun v : ℝ × (ℝ × ℝ) => H (v.1,v.2.1)) hF
  change (∫⁻ B in realPairNonrealEntrySet, realPairGaussianWeight n B*
    H (realPairCenter (Matrix.of B.curry),realPairHeightSq (Matrix.of B.curry)))=_ at he
  rw [he]
  congr 1
  apply lintegral_congr
  intro x
  let f := fun v : ℝ × ℝ => ENNReal.ofReal (Real.exp (-n*(x^2+v.1)))*
    (ENNReal.ofReal ((Real.sqrt (v.2+4*v.1))⁻¹)*
      ENNReal.ofReal (Real.exp (-(n/2)*v.2))*H (x,v.1))
  have hf : Measurable f := by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.mul
      · fun_prop
      · exact hH.comp (measurable_const.prodMk measurable_fst)
  change (∫⁻ v in realSchurPairCoordinateDomain, f v)=_
  rw [realPair_coordinateDomain_lintegral f hf]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only [f]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hroot : (Real.sqrt u)^2=u := Real.sq_sqrt hu.le
  have h := schurGap_raw_lintegral_eq_normalized n (Real.sqrt u) hn
    (Real.sqrt_pos.mpr hu) (fun _ => H (x,u)) measurable_const
  letI := schurSquaredGapLaw_probability n (Real.sqrt u) hn (Real.sqrt_pos.mpr hu)
  rw [hroot] at h
  simpa only [lintegral_const,measure_univ,mul_one,one_mul,mul_comm,mul_left_comm,mul_assoc] using h

#print axioms realPairGaussian_spectral_marginal
end SpectralRadiusUpperTail
