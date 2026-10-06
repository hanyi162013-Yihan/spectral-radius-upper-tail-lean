import SpectralRadiusUpperTail.RealSchurNativeSpectralDensity
import SpectralRadiusUpperTail.SchurGapKernelLIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

noncomputable def realSchurNativeSpectralFactor (q : ℕ) (n x u : ℝ) : ℝ :=
  if q=2 then (2*Real.pi)*Real.exp (-n*(x^2+u)) else Real.exp (-(n/2)*x^2)

noncomputable def realSchurNativeGapDensity (q : ℕ) (n u g : ℝ) : ℝ :=
  if q=2 then (Real.sqrt (g+4*u))⁻¹*Real.exp (-(n/2)*g) else 1

noncomputable def realSchurNativeGapLaw (q : ℕ) (n u : ℝ) : Measure ℝ :=
  if q=2 then schurSquaredGapLaw n (Real.sqrt u) else Measure.dirac 0

noncomputable def realSchurNativeGapNormalizer (q : ℕ) (n u : ℝ) : ℝ≥0∞ :=
  if q=2 then (ENNReal.ofReal (n/2))⁻¹*schurGapKernelNormalizer n (Real.sqrt u) else 1

theorem realSchurNativeSpectralDensity_factor (q : ℕ) (n x u g : ℝ) :
    realSchurNativeSpectralDensity q n (x,u,g)=
      realSchurNativeSpectralFactor q n x u*realSchurNativeGapDensity q n u g := by
  unfold realSchurNativeSpectralDensity realSchurNativeSpectralFactor realSchurNativeGapDensity
  split_ifs
  · rfl
  · exact (mul_one _).symm

theorem realSchurNativeSpectralFactor_nonneg (q : ℕ) (n x u : ℝ) :
    0 ≤ realSchurNativeSpectralFactor q n x u := by
  unfold realSchurNativeSpectralFactor
  split_ifs <;> positivity

theorem realSchurNativeGapDensity_nonneg (q : ℕ) (n u g : ℝ) :
    0 ≤ realSchurNativeGapDensity q n u g := by
  unfold realSchurNativeGapDensity
  split_ifs <;> positivity

theorem realSchurNativeGapDensity_measurable (q : ℕ) (n u : ℝ) :
    Measurable (realSchurNativeGapDensity q n u) := by
  unfold realSchurNativeGapDensity
  split_ifs <;> fun_prop

theorem realSchurNativeGapLaw_probability (q : ℕ) (n u : ℝ) (hn : 0 < n) (hu : q=2 → 0 < u) :
    IsProbabilityMeasure (realSchurNativeGapLaw q n u) := by
  unfold realSchurNativeGapLaw
  split_ifs with hq
  · exact schurSquaredGapLaw_probability n (Real.sqrt u) hn (Real.sqrt_pos.mpr (hu hq))
  · infer_instance

theorem realSchurNativeGapNormalizer_ne_top (q : ℕ) (n u : ℝ) (hn : 0 < n) (hu : q=2 → 0 < u) :
    realSchurNativeGapNormalizer q n u ≠ ∞ := by
  unfold realSchurNativeGapNormalizer
  split_ifs with hq
  · apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr (by positivity : 0 < n/2)).ne')
    · rw [schurGapKernelNormalizer_eq_ofReal n (Real.sqrt u) hn (Real.sqrt_pos.mpr (hu hq))]
      exact ENNReal.ofReal_ne_top
  · exact ENNReal.one_ne_top

/-- The raw gap factor is exactly a finite scalar times the normalized
Schur gap law; for scalar blocks both sides are the same Dirac measure. -/
theorem realSchurNativeGapDensity_measure (q : ℕ) (n u : ℝ) (hn : 0 < n) (hu : q=2 → 0 < u) :
    (realSchurNativeAuxiliaryBase q).withDensity (fun g => ENNReal.ofReal (realSchurNativeGapDensity q n u g)) =
      realSchurNativeGapNormalizer q n u • realSchurNativeGapLaw q n u := by
  by_cases hq : q=2
  · subst q
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _
      (realSchurNativeGapDensity_measurable 2 n u).ennreal_ofReal hF,lintegral_smul_measure,smul_eq_mul]
    simp only [realSchurNativeAuxiliaryBase,realSchurNativeGapDensity,realSchurNativeGapNormalizer,
      realSchurNativeGapLaw,ite_true]
    have hh := schurGap_raw_lintegral_eq_normalized n (Real.sqrt u) hn
      (Real.sqrt_pos.mpr (hu rfl)) F hF
    rw [Real.sq_sqrt (hu rfl).le] at hh
    convert hh using 1
    apply lintegral_congr
    intro g
    dsimp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt (g+4*u))⁻¹)]
    ac_rfl
  · simp [realSchurNativeAuxiliaryBase,realSchurNativeGapDensity,realSchurNativeGapNormalizer,
      realSchurNativeGapLaw,hq]

#print axioms realSchurNativeSpectralDensity_factor
#print axioms realSchurNativeGapLaw_probability
#print axioms realSchurNativeGapNormalizer_ne_top
#print axioms realSchurNativeGapDensity_measure
end SpectralRadiusUpperTail
