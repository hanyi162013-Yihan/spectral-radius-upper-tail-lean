import SpectralRadiusUpperTail.RealGaussianAtomicBlockArrayIntegral
import SpectralRadiusUpperTail.RealSchurAtomicNativeRotation

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal BigOperators

/-- Actual iid real Gaussian integration in scalar/nonreal-pair
spectral and gap coordinates. The full independent strictly-upper
Gaussian integral is retained inside the native core. -/
theorem realGaussian_lintegral_atomicSpectralCoordinates
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
            (∫⁻ v : Fin I.1.blockCount → ℝ × (ℝ × ℝ),
              realSchurAtomicNativeCore F I k (H I)
                (fun i => realSchurNativeCanonicalEntries (I.1.sizes i) (v i))
              ∂Measure.pi (fun i => realSchurNativeSpectralMeasure (I.1.sizes i) 1))) := by
  rw [realGaussian_lintegral_atomicBlockArrays n F g hg H hH hrep]
  apply Finset.sum_congr rfl
  intro I _
  apply tsum_congr
  intro k
  congr 2
  have he (a : ℝ) : -a/2=-(1/2 : ℝ)*a := by ring
  simp_rw [he]
  exact realSchurAtomicNativeCore_spectral_lintegral F I k (H I) (hH I) (hInv I)

#print axioms realGaussian_lintegral_atomicSpectralCoordinates
end SpectralRadiusUpperTail
