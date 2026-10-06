import SpectralRadiusUpperTail.RealSchurAtomicCoreWeight
import SpectralRadiusUpperTail.RealGaussianAtomicFiberFormula

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator ENNReal BigOperators

theorem realSchurAtomicDiagonal_core_lintegral
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (H : Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞) :
    (∫⁻ d in realSchurAtomicDiagonalSource I.1.sizes I.2.2,
      (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian I.1.sizes d) *
        realSchurAtomicDiagonalMultiplicityWeight F I k d) *
          realSchurGaussianUpperIntegral I.1.sizes H d) =
      ∫⁻ d, ENNReal.ofReal (Real.exp (-(∑ p : RealSchurMixedDiagonalEntry I.1.sizes, (d p)^2)/2)) *
        realSchurAtomicCoreWeight F I k H d := by
  classical
  rw [← lintegral_indicator (measurableSet_realSchurAtomicDiagonalSource I.1.sizes I.2.2)]
  apply lintegral_congr
  intro d
  by_cases hd : d ∈ realSchurAtomicDiagonalSource I.1.sizes I.2.2
  · simp only [realSchurAtomicCoreWeight,Set.indicator_of_mem hd]
    have hg : 0 ≤ realSchurMixedDiagonalGapWeight I.1.sizes d :=
      Finset.prod_nonneg (fun _ _ => abs_nonneg _)
    rw [realSchurMixedDiagonalGaussianJacobian_eq_gapWeight,ENNReal.ofReal_mul hg]
    ac_rfl
  · simp only [realSchurAtomicCoreWeight,Set.indicator_of_notMem hd,mul_zero]

/-- The full actual Gaussian atlas integral in independent native
diagonal-block arrays. All angular and strict-upper integration has been
accounted for in the displayed angular mass and invariant core weight. -/
theorem realGaussian_lintegral_atomicBlockArrays
    (n : ℕ) (F : RealSchurFiniteAtlas n)
    (g : ((Fin n × Fin n) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (H : ∀ I : RealSchurFiniteCode n,
      Matrix (RealSchurMixedCoord I.1.sizes) (RealSchurMixedCoord I.1.sizes) ℝ → ℝ≥0∞)
    (hH : ∀ I, Measurable (H I))
    (hrep : ∀ I k t, t ∈ F.atomicSource I k → g (F.output I k t)=H I t.2.val) :
    (∫⁻ x, g x ∂gaussianMatrixLaw n) =
      ∑ I : RealSchurFiniteCode n, ∑' k,
        (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(n*n)))⁻¹ *
          ((∫⁻ w in realSchurMixedFlagAnglePatch I.1.sizes I.1.sizes_pos
            (F.marker I) (F.marker_injective I) (F.frames I) k,
              ENNReal.ofReal |realSchurMixedAngularJacobian I.1.sizes w|) *
            (∫⁻ D : (i : Fin I.1.blockCount) → (Fin (I.1.sizes i) × Fin (I.1.sizes i)) → ℝ,
              ENNReal.ofReal (∏ i : Fin I.1.blockCount,
                Real.exp (-(∑ ab : Fin (I.1.sizes i) × Fin (I.1.sizes i), (D i ab)^2)/2)) *
                  realSchurAtomicCoreWeight F I k (H I)
                    ((realSchurMixedDiagonalProductEquiv I.1.sizes).symm D))) := by
  rw [realGaussian_lintegral_atomicFibers n F g hg H hH hrep]
  apply Finset.sum_congr rfl
  intro I _
  apply tsum_congr
  intro k
  congr 2
  change (∫⁻ d in realSchurAtomicDiagonalSource I.1.sizes I.2.2,
    (ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian I.1.sizes d) *
      realSchurAtomicDiagonalMultiplicityWeight F I k d) *
        realSchurGaussianUpperIntegral I.1.sizes (H I) d) = _
  rw [realSchurAtomicDiagonal_core_lintegral F I k (H I),
    realSchurMixedDiagonalProduct_lintegral I.1.sizes]
  simp only [realSchurMixedDiagonal_gaussian_product,MeasurableEquiv.apply_symm_apply]

#print axioms realSchurAtomicDiagonal_core_lintegral
#print axioms realGaussian_lintegral_atomicBlockArrays
end SpectralRadiusUpperTail
