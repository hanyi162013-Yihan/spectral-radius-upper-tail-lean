import SpectralRadiusUpperTail.MarkedNonrealDiagonalSplit
import SpectralRadiusUpperTail.MarkedNonrealAtlasWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

noncomputable def markedNonrealPairComplementKernel (m : ℕ) (g : ℂ → ℝ≥0∞)
    (p : ((Fin 2 × Fin 2) → ℝ) × ((Fin m × Fin m) → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal |(realSchurRectangularSylvester (Matrix.of p.2.curry)
    (Matrix.of p.1.curry)).det| *
    (ENNReal.ofReal (realMatrixGaussianWeight (Fin 2) (Matrix.of p.1.curry))*
      ENNReal.ofReal (realMatrixGaussianWeight (Fin m) (Matrix.of p.2.curry))) *
        markedNonrealBlockWeight (Matrix.of p.1.curry) g

theorem markedNonrealDiagonal_integrand_split (m : ℕ) (g : ℂ → ℝ≥0∞)
    (d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ) :
    ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d)*
      markedNonrealDiagonalWeight m g d =
      markedNonrealPairComplementKernel m g (markedNonrealDiagonalSplit m d) := by
  rw [markedNonrealDiagonalJacobian_factor,markedNonrealDiagonalWeight,
    markedNonrealDiagonalSplit_first]
  simp only [markedNonrealPairComplementKernel,realMatrixGaussianWeight,
    ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem markedNonrealPairComplementKernel_measurable
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (markedNonrealPairComplementKernel m g) := by
  have h := ((realSchurMixedDiagonalGaussianJacobian_continuous
      (markedNonrealBlockSizes m)).measurable.ennreal_ofReal.mul
    (markedNonrealDiagonalWeight_measurable m g hg)).comp
      (markedNonrealDiagonalSplit m).symm.measurable
  convert h using 1
  funext p
  dsimp only [Function.comp_def,Pi.mul_apply]
  rw [markedNonrealDiagonal_integrand_split,MeasurableEquiv.apply_symm_apply]

/-- Tonelli separates the selected two-plane block from the unrestricted
Gaussian complementary matrix. -/
theorem markedNonrealDiagonal_lintegral_split
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ d : RealSchurMixedDiagonalEntry (markedNonrealBlockSizes m) → ℝ,
      ENNReal.ofReal (realSchurMixedDiagonalGaussianJacobian (markedNonrealBlockSizes m) d)*
        markedNonrealDiagonalWeight m g d) =
      ∫⁻ B : (Fin 2 × Fin 2) → ℝ, ∫⁻ H : (Fin m × Fin m) → ℝ,
        markedNonrealPairComplementKernel m g (B,H) := by
  rw [MeasurePreserving.lintegral_map_equiv _ (markedNonrealDiagonalSplit m).symm
    (markedNonrealDiagonalSplit_measurePreserving m).symm]
  simp_rw [markedNonrealDiagonal_integrand_split,MeasurableEquiv.apply_symm_apply]
  rw [Measure.volume_eq_prod]
  exact lintegral_prod _ (markedNonrealPairComplementKernel_measurable m g hg).aemeasurable

#print axioms markedNonrealDiagonal_integrand_split
#print axioms markedNonrealPairComplementKernel_measurable
#print axioms markedNonrealDiagonal_lintegral_split
end SpectralRadiusUpperTail
