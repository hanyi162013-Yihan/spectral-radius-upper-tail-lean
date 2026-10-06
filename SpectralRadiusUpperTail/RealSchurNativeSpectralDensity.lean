import SpectralRadiusUpperTail.RealPairSpectralGapDensity
import SpectralRadiusUpperTail.RealSchurScalarSpectralIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

/-- Scalar blocks carry dummy zero coordinates; genuine pair blocks
carry positive imaginary-square and gap coordinates. -/
noncomputable def realSchurNativeAuxiliaryBase (q : ℕ) : Measure ℝ :=
  if q=2 then volume.restrict (Set.Ioi 0) else Measure.dirac 0

noncomputable def realSchurNativeSpectralBase (q : ℕ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume : Measure ℝ).prod ((realSchurNativeAuxiliaryBase q).prod (realSchurNativeAuxiliaryBase q))

noncomputable def realSchurNativeSpectralDensity (q : ℕ) (n : ℝ) (v : ℝ × (ℝ × ℝ)) : ℝ :=
  if q=2 then realPairSpectralGapDensity n v else Real.exp (-(n/2)*v.1^2)

instance realSchurNativeAuxiliaryBase_sigmaFinite (q : ℕ) : SigmaFinite (realSchurNativeAuxiliaryBase q) := by
  unfold realSchurNativeAuxiliaryBase
  split_ifs <;> infer_instance

instance realSchurNativeSpectralBase_sigmaFinite (q : ℕ) : SigmaFinite (realSchurNativeSpectralBase q) := by
  unfold realSchurNativeSpectralBase
  infer_instance

theorem realSchurNativeSpectralDensity_measurable (q : ℕ) (n : ℝ) :
    Measurable (realSchurNativeSpectralDensity q n) := by
  unfold realSchurNativeSpectralDensity
  split_ifs
  · exact realPairSpectralGapDensity_measurable n
  · fun_prop

theorem realSchurNativeSpectralDensity_nonneg (q : ℕ) (n : ℝ) (v : ℝ × (ℝ × ℝ)) :
    0 ≤ realSchurNativeSpectralDensity q n v := by
  unfold realSchurNativeSpectralDensity
  split_ifs
  · exact realPairSpectralGapDensity_nonneg n v
  · exact (Real.exp_pos _).le

theorem realSchurNativeSpectralBase_two : realSchurNativeSpectralBase 2=realPairSpectralGapBase := by
  simp only [realSchurNativeSpectralBase,realSchurNativeAuxiliaryBase,ite_true,
    Measure.prod_restrict]
  rfl

/-- Uniform explicit density for both possible native block sizes. -/
theorem realSchurNativeSpectralMeasure_eq_density (q : ℕ) (hq : q=1 ∨ q=2) (n : ℝ) :
    realSchurNativeSpectralMeasure q n=(realSchurNativeSpectralBase q).withDensity
      (fun v => ENNReal.ofReal (realSchurNativeSpectralDensity q n v)) := by
  rcases hq with rfl | rfl
  · apply Measure.ext_of_lintegral
    intro F hF
    rw [realSchurNativeSpectralMeasure_one_lintegral n F hF,
      lintegral_withDensity_eq_lintegral_mul _ (realSchurNativeSpectralDensity_measurable 1 n).ennreal_ofReal hF]
    simp only [realSchurNativeSpectralBase,realSchurNativeAuxiliaryBase,show ¬(1 : ℕ)=2 by decide,
      ite_false,Measure.dirac_prod_dirac]
    change (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(n/2)*x^2))*F (x,0,0)) =
      ∫⁻ v : ℝ × (ℝ × ℝ), ENNReal.ofReal (realSchurNativeSpectralDensity 1 n v)*F v
        ∂(volume : Measure ℝ).prod (Measure.dirac (0,0))
    rw [lintegral_prod (fun v : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (realSchurNativeSpectralDensity 1 n v)*F v)
        ((realSchurNativeSpectralDensity_measurable 1 n).ennreal_ofReal.mul hF).aemeasurable]
    simp only [lintegral_dirac,realSchurNativeSpectralDensity,show ¬(1 : ℕ)=2 by decide,ite_false]
  · rw [realSchurNativeSpectralMeasure_two,realSchurNativeSpectralBase_two,
      realPairSpectralGapMeasure_eq_density]
    rfl

theorem realSchurNativeSpectralDensity_integrable (q : ℕ) (hq : q=1 ∨ q=2)
    (n : ℝ) (hn : 0 < n) :
    Integrable (realSchurNativeSpectralDensity q n) (realSchurNativeSpectralBase q) := by
  let := realSchurNativeSpectralMeasure_finite q n hn
  apply (lintegral_ofReal_ne_top_iff_integrable
    (realSchurNativeSpectralDensity_measurable q n).aestronglyMeasurable
    (Filter.Eventually.of_forall (realSchurNativeSpectralDensity_nonneg q n))).mp
  have hh := measure_ne_top (realSchurNativeSpectralMeasure q n) Set.univ
  rw [realSchurNativeSpectralMeasure_eq_density q hq n,withDensity_apply _ MeasurableSet.univ] at hh
  simpa only [Measure.restrict_univ] using hh

#print axioms realSchurNativeSpectralMeasure_eq_density
#print axioms realSchurNativeSpectralDensity_integrable
end SpectralRadiusUpperTail
