import SpectralRadiusUpperTail.RealSchurNativeScaledMatrix

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius ENNReal

theorem realSchurNativeCommonLaw_probability {m : ℕ} (s : Fin m → ℕ) (u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) : IsProbabilityMeasure (realSchurNativeCommonLaw s u) := by
  let : ∀ i, IsProbabilityMeasure (realSchurNativeGapLaw (s i) 1 (u i)) :=
    fun i => realSchurNativeGapLaw_probability (s i) 1 (u i) (by norm_num) (hu i)
  unfold realSchurNativeCommonLaw
  infer_instance

theorem realSchurNativeCommonLaw_positive {m : ℕ} (s : Fin m → ℕ) (u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    ∀ᵐ z ∂realSchurNativeCommonLaw s u, ∀ i, s i=2 → 0 < z.1 i :=
  (Measure.quasiMeasurePreserving_fst (μ := Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i)))
    (ν := Measure.pi (fun _ : SchurEntryIndex m 2 => standardNormal))).ae
      (realSchurNativeGapProduct_positive s 1 (by norm_num) u hu)

theorem realSchurNativeRadiusObservable_measurable {m : ℕ} (s : Fin m → ℕ)
    (n k : ℕ) (η : ℝ) : Measurable
      (fun A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
        ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k))) := by
  have hr : Measurable (fun A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      finiteRealMatrixRadius ((1/Real.sqrt n) • A)) :=
    finiteRealMatrixRadius_measurable.comp (by fun_prop)
  exact (((measurable_const.max hr).add_const η).pow_const _).ennreal_ofReal

/-- The buffered radius is constant under the actual conditional
probability law, with precisely the diagonal radius of the padded model. -/
theorem realSchurConditionalNative_radius_model {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n k : ℕ) (hn : 0 < n) (η : ℝ) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    realSchurConditionalNativeIntegral s
      (fun A => ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) • A))+η)^(2*k))) x u=
      realSchurUpperGaussianMass s*ENNReal.ofReal
        ((max 1 (realSchurDataIntrinsicRadius
          (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))))+η)^(2*k)) := by
  have hH := realSchurNativeRadiusObservable_measurable s n k η
  rw [realSchurConditionalNativeIntegral_eq_probability s x u hu _ hH]
  congr 1
  have hm : Measurable (fun z : (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) =>
      ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) •
        realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1) z.2))+η)^(2*k))) :=
    hH.comp (realSchurCanonicalJoin_continuous s x u).measurable
  rw [← (realSchurNativeCommonSelect_measurePreserving s hsmall u hu).lintegral_comp hm]
  let := realSchurNativeCommonLaw_probability s u hu
  have he : (fun z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ) =>
      ENNReal.ofReal ((max 1 (finiteRealMatrixRadius ((1/Real.sqrt n) •
        realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u z.1)
          (realSchurNativeUpperSelect s hsmall z.2)))+η)^(2*k))) =ᵐ[realSchurNativeCommonLaw s u]
      (fun _ => ENNReal.ofReal ((max 1 (realSchurDataIntrinsicRadius
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))))+η)^(2*k))) := by
    filter_upwards [realSchurNativeCommonLaw_positive s u hu] with z hz
    rw [realSchurNative_scaled_radius_identity s hs hsmall n hn x u
      (fun i hi => (hu i hi).le) z (fun i hi => (hz i hi).le)]
  dsimp only [realSchurNativeCommonSelect]
  rw [lintegral_congr_ae he,lintegral_const,measure_univ,mul_one]

#print axioms realSchurNativeCommonLaw_probability
#print axioms realSchurNativeCommonLaw_positive
#print axioms realSchurNativeRadiusObservable_measurable
#print axioms realSchurConditionalNative_radius_model
end SpectralRadiusUpperTail
