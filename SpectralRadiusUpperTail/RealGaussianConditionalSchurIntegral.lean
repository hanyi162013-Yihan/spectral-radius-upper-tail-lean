import SpectralRadiusUpperTail.RealGaussianAtomicSpectralIntegral
import SpectralRadiusUpperTail.RealSchurAtomicConditionalIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal BigOperators

/-- The conditional integral over independent pair gaps and all
strict-upper entries, in unscaled Gaussian entry coordinates. -/
noncomputable def realSchurConditionalNativeIntegral {m : ℕ} (s : Fin m → ℕ)
    (H : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ → ℝ≥0∞)
    (x u : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ g, realSchurGaussianUpperIntegral s H (realSchurCanonicalDiagonal s x u g)
    ∂Measure.pi (fun i => realSchurNativeGapLaw (s i) 1 (u i))

/-- The remaining spectral weight includes the exact overlap correction
of the complete atomic atlas. It contains no gap or upper-entry variable. -/
noncomputable def realSchurAtomicConditionalWeight
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (x u : Fin I.1.blockCount → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i : Fin I.1.blockCount, realSchurNativeSpectralFactor (I.1.sizes i) 1 (x i) (u i))*
    ((∏ i : Fin I.1.blockCount, realSchurNativeGapNormalizer (I.1.sizes i) 1 (u i))*
      realSchurAtomicSpectralWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u (fun _ => 1)))

/-- Exact conditional Schur integral representation of the actual iid
real Gaussian law for conjugation-invariant observables. All independent
gap laws and strict-upper Gaussian integrations have been derived from
the original matrix density, rather than assumed as an external input. -/
theorem realGaussian_lintegral_conditionalSchur
    (n : ℕ) (F : RealSchurFiniteAtlas n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (H : ∀ I : RealSchurFiniteCode n,
      Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : ∀ I, Measurable (H I))
    (hInv : ∀ I (W : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ),
      Wᵀ*W=1 → ∀ A, H I (W*A*Wᵀ)=H I A)
    (hrep : ∀ I k t, t ∈ F.atomicSource I k → g (F.output I k t)=H I t.2.val) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n, ∑' k,
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(n*n)))⁻¹ *
          ((∫⁻ w in realSchurMixedFlagAnglePatch I.1.sizes I.1.sizes_pos
            (F.marker I) (F.marker_injective I) (F.frames I) k,
              ENNReal.ofReal |realSchurMixedAngularJacobian I.1.sizes w|) *
            (∫⁻ x : Fin I.1.blockCount → ℝ, ∫⁻ u,
              realSchurAtomicConditionalWeight F I k x u*
                realSchurConditionalNativeIntegral I.1.sizes (H I) x u
              ∂Measure.pi (fun i => realSchurNativeAuxiliaryBase (I.1.sizes i)))) := by
  rw [realGaussian_lintegral_atomicSpectralCoordinates n F g hg H hH hInv hrep]
  apply Finset.sum_congr rfl
  intro I _
  apply tsum_congr
  intro k
  congr 2
  rw [realSchurAtomicNativeCore_conditional_lintegral F I k (H I) (hH I)]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro u
  unfold realSchurAtomicConditionalWeight realSchurConditionalNativeIntegral
  ac_rfl

#print axioms realGaussian_lintegral_conditionalSchur
end SpectralRadiusUpperTail
