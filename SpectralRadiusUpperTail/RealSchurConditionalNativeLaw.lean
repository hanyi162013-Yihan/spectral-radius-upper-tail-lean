import SpectralRadiusUpperTail.RealGaussianConditionalSchurIntegral
import SpectralRadiusUpperTail.FiniteGaussianRawIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

noncomputable def realSchurNativeConditionalLaw {m : ℕ} (s : Fin m → ℕ)
    (u : Fin m → ℝ) :
    Measure ((Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ)) :=
  (Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i))).prod
    (Measure.pi (fun _ => standardNormal))

noncomputable def realSchurUpperGaussianMass {m : ℕ} (s : Fin m → ℕ) : ℝ≥0∞ :=
  ∫⁻ v : RealSchurMixedStrictUpperEntry s → ℝ,
    ENNReal.ofReal (Real.exp (-(∑ p, (v p)^2)/2))

theorem realSchurUpperGaussianMass_ne_top {m : ℕ} (s : Fin m → ℕ) :
    realSchurUpperGaussianMass s ≠ ∞ := by
  have hi := realArrayGaussianWeight_integrable (ι := RealSchurMixedStrictUpperEntry s)
    1 (by norm_num)
  have he : (fun v : RealSchurMixedStrictUpperEntry s → ℝ => Real.exp (-(∑ p, (v p)^2)/2))=
      (fun v => Real.exp (-(1/2)*∑ p, (v p)^2)) := by
    funext v
    congr 1
    ring
  unfold realSchurUpperGaussianMass
  simp_rw [congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

theorem realSchurCanonicalJoin_continuous {m : ℕ} (s : Fin m → ℕ)
    (x u : Fin m → ℝ) : Continuous
      (fun z : (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) =>
        realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1) z.2) :=
  (realSchurMixedUpperEntryJoin_continuous s).comp
    (((realSchurCanonicalDiagonal_continuous_gap s x u).comp continuous_fst).prodMk continuous_snd)

theorem realSchurGaussianUpperIntegral_eq_probability {m : ℕ} (s : Fin m → ℕ)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hH : Measurable H) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    realSchurGaussianUpperIntegral s H d=realSchurUpperGaussianMass s*
      ∫⁻ v, H (realSchurMixedUpperEntryJoin s d v)
        ∂Measure.pi (fun _ : RealSchurMixedStrictUpperEntry s => standardNormal) := by
  have hc : Continuous (fun v : RealSchurMixedStrictUpperEntry s → ℝ =>
      realSchurMixedUpperEntryJoin s d v) :=
    (realSchurMixedUpperEntryJoin_continuous s).comp (continuous_const.prodMk continuous_id)
  have hm : Measurable (fun v : RealSchurMixedStrictUpperEntry s → ℝ =>
      H (realSchurMixedUpperEntryJoin s d v)) := hH.comp hc.measurable
  exact finiteGaussian_raw_lintegral _ hm

/-- The conditional integral differs from a probability integral only by
the total mass of the raw strict-upper Gaussian density. -/
theorem realSchurConditionalNativeIntegral_eq_probability {m : ℕ} (s : Fin m → ℕ)
    (x u : Fin m → ℝ) (hu : ∀ i, s i=2 → 0 < u i)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    realSchurConditionalNativeIntegral s H x u=
      realSchurUpperGaussianMass s*
        ∫⁻ z, H (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1) z.2)
          ∂realSchurNativeConditionalLaw s u := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) 1 (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) 1 (u i) (by norm_num) (hu i)
  have hm : Measurable (fun z : (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) =>
      H (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1) z.2)) :=
    hH.comp (realSchurCanonicalJoin_continuous s x u).measurable
  change (∫⁻ g, realSchurGaussianUpperIntegral s H (realSchurCanonicalDiagonal s x u g)
    ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i)))=_
  simp_rw [realSchurGaussianUpperIntegral_eq_probability s H hH]
  rw [lintegral_const_mul' _ _ (realSchurUpperGaussianMass_ne_top s)]
  congr 1
  exact (lintegral_prod
    (fun z : (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) =>
      H (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1) z.2))
    hm.aemeasurable).symm

#print axioms realSchurUpperGaussianMass_ne_top
#print axioms realSchurCanonicalJoin_continuous
#print axioms realSchurConditionalNativeIntegral_eq_probability
end SpectralRadiusUpperTail
