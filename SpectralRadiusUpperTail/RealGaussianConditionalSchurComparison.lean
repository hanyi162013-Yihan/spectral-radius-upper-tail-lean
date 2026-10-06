import SpectralRadiusUpperTail.RealGaussianConditionalSchurIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal

theorem realSchurConditionalNativeIntegral_const_mul {m : ℕ} (s : Fin m → ℕ)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (x u : Fin m → ℝ) :
    realSchurConditionalNativeIntegral s (fun A => C*H A) x u=
      C*realSchurConditionalNativeIntegral s H x u := by
  unfold realSchurConditionalNativeIntegral realSchurGaussianUpperIntegral
  have he (g : Fin m → ℝ) (v : RealSchurMixedStrictUpperEntry s → ℝ) :
      ENNReal.ofReal (Real.exp (-(∑ p, (v p)^2)/2)) *
        (C*H (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u g) v))=
      C*(ENNReal.ofReal (Real.exp (-(∑ p, (v p)^2)/2))*
        H (realSchurMixedUpperEntryJoin s (realSchurCanonicalDiagonal s x u g) v)) := by ac_rfl
  simp_rw [he,lintegral_const_mul' C _ hC]

/-- Pointwise comparison of the derived conditional integrals transfers
to the actual iid Gaussian matrix law with all atlas weights included. -/
theorem realGaussian_lintegral_conditionalSchur_compare
    (n : ℕ) (F : RealSchurFiniteAtlas n)
    (g₁ g₂ : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (H₁ H₂ : ∀ I : RealSchurFiniteCode n,
      Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH₁ : ∀ I, Measurable (H₁ I)) (hH₂ : ∀ I, Measurable (H₂ I))
    (hInv₁ : ∀ I (W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ),
      Wᵀ*W=1 → ∀ A, H₁ I (W*A*Wᵀ)=H₁ I A)
    (hInv₂ : ∀ I (W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ),
      Wᵀ*W=1 → ∀ A, H₂ I (W*A*Wᵀ)=H₂ I A)
    (hrep₁ : ∀ I j t, t ∈ F.atomicSource I j → g₁ (F.output I j t)=H₁ I t.2.val)
    (hrep₂ : ∀ I j t, t ∈ F.atomicSource I j → g₂ (F.output I j t)=H₂ I t.2.val)
    (hcond : ∀ I x u, (∀ i, I.1.sizes i=2 → 0 < u i) →
      realSchurConditionalNativeIntegral I.1.sizes (H₁ I) x u ≤
        realSchurConditionalNativeIntegral I.1.sizes (H₂ I) x u) :
    (∫⁻ a, g₁ a ∂gaussianMatrixLaw n) ≤ ∫⁻ a, g₂ a ∂gaussianMatrixLaw n := by
  rw [realGaussian_lintegral_conditionalSchur n F g₁ hg₁ H₁ hH₁ hInv₁ hrep₁,
    realGaussian_lintegral_conditionalSchur n F g₂ hg₂ H₂ hH₂ hInv₂ hrep₂]
  apply Finset.sum_le_sum
  intro I _
  apply ENNReal.tsum_le_tsum
  intro j
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro x
  apply lintegral_mono_ae
  filter_upwards [realSchurNativeAuxiliaryProduct_positive I.1.sizes] with u hu
  exact mul_le_mul' le_rfl (hcond I x u hu)

#print axioms realSchurConditionalNativeIntegral_const_mul
#print axioms realGaussian_lintegral_conditionalSchur_compare
end SpectralRadiusUpperTail
