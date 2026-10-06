import SpectralRadiusUpperTail.RealSchurNativeMatrixTransfer
import SpectralRadiusUpperTail.RealSchurNativeProbabilityTransport
import SpectralRadiusUpperTail.RealSchurPaddedContinuity

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Frobenius ENNReal

theorem realSchurNative_scaled_power_identity {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 ≤ u i)
    (z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ)) (hg : ∀ i, s i=2 → 0 ≤ z.1 i) :
    ‖((1/Real.sqrt n) • realSchurMixedUpperEntryJoin s
      (realSchurCanonicalDiagonal s x u z.1) (realSchurNativeUpperSelect s hsmall z.2))^k‖^2=
      ‖(flattenSchurBlocks (realSchurPaddedMatrix n
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ)))
          (realSchurNativeCommonScale n z)))^k‖^2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := realSchurNativePadded_power_norm_sq s hs hsmall n k hk
    (fun i => x i/Real.sqrt n) (fun i => u i/(n : ℝ))
    (fun i hi => div_nonneg (hu i hi) hnR.le) (realSchurNativeCommonScale n z)
    (fun i hi => div_nonneg (hg i hi) hnR.le)
  change _=‖(realSchurMixedUpperEntryJoin s
    (realSchurCanonicalDiagonal s (fun i => x i/Real.sqrt n) (fun i => u i/(n : ℝ))
      (fun i => z.1 i/(n : ℝ)))
    (fun p => realSchurNativeUpperSelect s hsmall z.2 p/Real.sqrt n))^k‖^2 at hh
  rw [realSchurCanonicalJoin_scale s x u z.1 _ (n : ℝ) hnR] at hh
  exact hh.symm

/-- The exact native conditional power integral is the already studied
independent padded-model moment, times the raw upper-density mass. -/
theorem realSchurConditionalNative_power_model {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (hsmall : ∀ i, s i ≤ 2)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i) :
    realSchurConditionalNativeIntegral s
      (fun A => ENNReal.ofReal (‖((1/Real.sqrt n) • A)^k‖^2)) x u=
      realSchurUpperGaussianMass s*
        ∫⁻ z, ENNReal.ofReal (‖(flattenSchurBlocks (realSchurPaddedMatrix n
          (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))) z))^k‖^2)
          ∂realSchurGlobalLaw n
            (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))) := by
  have hH : Measurable (fun A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
      ENNReal.ofReal (‖((1/Real.sqrt n) • A)^k‖^2)) := by fun_prop
  rw [realSchurConditionalNativeIntegral_eq_probability s x u hu _ hH]
  congr 1
  have hm : Measurable (fun z : (Fin m → ℝ) × (RealSchurMixedStrictUpperEntry s → ℝ) =>
      ENNReal.ofReal (‖((1/Real.sqrt n) • realSchurMixedUpperEntryJoin s
        (realSchurCanonicalDiagonal s x u z.1) z.2)^k‖^2)) :=
    hH.comp (realSchurCanonicalJoin_continuous s x u).measurable
  have hmodel : Measurable (fun z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ) =>
      ENNReal.ofReal (‖(flattenSchurBlocks (realSchurPaddedMatrix n
        (fun i => realSchurNativeBlockData (s i) (x i/Real.sqrt n) (u i/(n : ℝ))) z))^k‖^2)) :=
    (realSchurFlattenedPowerEnergy_continuous n k _).measurable.ennreal_ofReal
  rw [← (realSchurNativeCommonSelect_measurePreserving s hsmall u hu).lintegral_comp hm,
    ← (realSchurNativeCommonScale_measurePreserving s n hn x u hu).lintegral_comp hmodel]
  have hpositive : ∀ᵐ z ∂realSchurNativeCommonLaw s u,
      ∀ i, s i=2 → 0 < z.1 i :=
    (Measure.quasiMeasurePreserving_fst (μ := Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i)))
      (ν := Measure.pi (fun _ : SchurEntryIndex m 2 => standardNormal))).ae
      (realSchurNativeGapProduct_positive s 1 (by norm_num) u hu)
  apply lintegral_congr_ae
  filter_upwards [hpositive] with z hz
  exact congrArg ENNReal.ofReal (realSchurNative_scaled_power_identity s hs hsmall n k hn hk x u
    (fun i hi => (hu i hi).le) z (fun i hi => (hz i hi).le))

#print axioms realSchurNative_scaled_power_identity
#print axioms realSchurConditionalNative_power_model
end SpectralRadiusUpperTail
