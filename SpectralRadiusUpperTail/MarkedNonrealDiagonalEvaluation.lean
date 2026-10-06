import SpectralRadiusUpperTail.MarkedNonrealComplementMoment
import SpectralRadiusUpperTail.MarkedNonrealPairReference
import SpectralRadiusUpperTail.MarkedNonrealGaussianArea

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix

noncomputable def markedNonrealComplementMass (m : ℕ) : ℝ≥0∞ :=
  realMatrixRawGaussianMass (Fin m)*ENNReal.ofReal (m.factorial : ℝ)

theorem markedNonrealComplementMass_ne_top (m : ℕ) : markedNonrealComplementMass m ≠ ∞ := by
  unfold markedNonrealComplementMass realMatrixRawGaussianMass
  rw [realSchurMixedIndependentGaussianLIntegral]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem realPairGaussianWeight_one_eq_matrix (B : (Fin 2 × Fin 2) → ℝ) :
    realPairGaussianWeight 1 B=
      ENNReal.ofReal (realMatrixGaussianWeight (Fin 2) (Matrix.of B.curry)) := by
  unfold realPairGaussianWeight realMatrixGaussianWeight
  congr 2
  change -(1/2)*(∑ p, (B p)^2)=-(∑ p, (B p)^2)/2
  ring

/-- The unrestricted complementary-matrix integral is evaluated exactly;
only an actual four-entry nonreal-block integral remains. -/
theorem markedNonrealDiagonalIntegral_eq_pairTest
    (m : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    markedNonrealDiagonalIntegral m g=
      markedNonrealComplementMass m*markedNonrealPairTestIntegral m g := by
  unfold markedNonrealDiagonalIntegral
  rw [markedNonrealDiagonal_lintegral_split m g hg]
  simp_rw [markedNonrealComplement_kernel_inner]
  let f := fun B : (Fin 2 × Fin 2) → ℝ => realPairGaussianWeight 1 B*
    (ENNReal.ofReal (ginibreExpPartial (m+1)
      ((realPairCenter (Matrix.of B.curry))^2+realPairHeightSq (Matrix.of B.curry)))*
        g (realPairUpperRoot (Matrix.of B.curry)))
  have hp (B : (Fin 2 × Fin 2) → ℝ) :
      (ENNReal.ofReal (realMatrixGaussianWeight (Fin 2) (Matrix.of B.curry))*
        markedNonrealBlockWeight (Matrix.of B.curry) g)*
          (realMatrixRawGaussianMass (Fin m)*ENNReal.ofReal ((m.factorial : ℝ)*
            ginibreExpPartial (m+1) ((realPairCenter (Matrix.of B.curry))^2+
              realPairHeightSq (Matrix.of B.curry)))) =
      markedNonrealComplementMass m*realPairNonrealEntrySet.indicator f B := by
    by_cases hB : B ∈ realPairNonrealEntrySet
    · rw [Set.indicator_of_mem hB]
      change 0 < realPairHeightSq (Matrix.of B.curry) at hB
      rw [markedNonrealBlockWeight,if_pos hB,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ m.factorial)]
      dsimp only [markedNonrealComplementMass,f]
      rw [realPairGaussianWeight_one_eq_matrix]
      ac_rfl
    · rw [Set.indicator_of_notMem hB]
      change ¬0 < realPairHeightSq (Matrix.of B.curry) at hB
      simp [markedNonrealBlockWeight,hB]
  simp_rw [hp]
  rw [lintegral_const_mul' _ _ (markedNonrealComplementMass_ne_top m),
    lintegral_indicator measurableSet_realPairNonrealEntrySet]
  rfl

#print axioms markedNonrealComplementMass_ne_top
#print axioms realPairGaussianWeight_one_eq_matrix
#print axioms markedNonrealDiagonalIntegral_eq_pairTest
end SpectralRadiusUpperTail
