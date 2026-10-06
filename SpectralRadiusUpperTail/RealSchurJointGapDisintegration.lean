import SpectralRadiusUpperTail.RealSchurJointSpectralDensity
import SpectralRadiusUpperTail.RealSchurGapProductIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

theorem realSchurNativeAuxiliaryBase_positive (q : ℕ) :
    ∀ᵐ u ∂realSchurNativeAuxiliaryBase q, q=2 → 0 < u := by
  by_cases hq : q=2
  · subst q
    change ∀ᵐ u ∂(volume : Measure ℝ).restrict (Set.Ioi 0), (2 : ℕ)=2 → 0 < u
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact fun _ => hu
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (hq h))

theorem realSchurNativeAuxiliaryProduct_positive {m : ℕ} (s : Fin m → ℕ) :
    ∀ᵐ u ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i)),
      ∀ i, s i=2 → 0 < u i := by
  apply ae_all_iff.mpr
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun j => realSchurNativeAuxiliaryBase (s j)) i).ae
    (realSchurNativeAuxiliaryBase_positive (s i))

theorem realSchurNativeJointGap_inner_lintegral
    {m : ℕ} (s : Fin m → ℕ) (n : ℝ) (hn : 0 < n) (x u : Fin m → ℝ)
    (hu : ∀ i, s i=2 → 0 < u i)
    (H : (Fin m → ℝ × (ℝ × ℝ)) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g, ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (x i,u i,g i))*
      H (fun i => (x i,u i,g i)) ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i))) =
      ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralFactor (s i) n (x i) (u i))*
        ((∏ i : Fin m, realSchurNativeGapNormalizer (s i) n (u i))*
          ∫⁻ g, H (fun i => (x i,u i,g i)) ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) n (u i))) := by
  have he (g : Fin m → ℝ) :
      ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralDensity (s i) n (x i,u i,g i))*
        H (fun i => (x i,u i,g i)) =
      ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralFactor (s i) n (x i) (u i))*
        (ENNReal.ofReal (∏ i : Fin m, realSchurNativeGapDensity (s i) n (u i) (g i))*
          H (fun i => (x i,u i,g i))) := by
    simp_rw [realSchurNativeSpectralDensity_factor]
    rw [Finset.prod_mul_distrib,ENNReal.ofReal_mul
      (Finset.prod_nonneg (fun i _ => realSchurNativeSpectralFactor_nonneg (s i) n (x i) (u i)))]
    exact mul_assoc _ _ _
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  apply realSchurNativeGapProduct_lintegral s n hn u hu
  apply hH.comp
  fun_prop

/-- The full joint block law, conditioned on the real and imaginary
parts, has independent normalized Schur gaps. All normalization factors
are displayed in the outer spectral weight. -/
theorem realSchurNativeSpectralProduct_disintegration
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2) (n : ℝ) (hn : 0 < n)
    (H : (Fin m → ℝ × (ℝ × ℝ)) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ v, H v ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (s i) n)) =
      ∫⁻ x : Fin m → ℝ, ∫⁻ u,
        ENNReal.ofReal (∏ i : Fin m, realSchurNativeSpectralFactor (s i) n (x i) (u i))*
          ((∏ i : Fin m, realSchurNativeGapNormalizer (s i) n (u i))*
            ∫⁻ g, H (fun i => (x i,u i,g i)) ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) n (u i)))
        ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (s i)) := by
  rw [realSchurNativeSpectralProduct_lintegral s hs n hn H hH]
  apply lintegral_congr
  intro x
  apply lintegral_congr_ae
  filter_upwards [realSchurNativeAuxiliaryProduct_positive s] with u hu
  exact realSchurNativeJointGap_inner_lintegral s n hn x u hu H hH

#print axioms realSchurNativeAuxiliaryProduct_positive
#print axioms realSchurNativeJointGap_inner_lintegral
#print axioms realSchurNativeSpectralProduct_disintegration
end SpectralRadiusUpperTail
