import SpectralRadiusUpperTail.MarkedNonrealComplementIntegral
import SpectralRadiusUpperTail.GaussianQuadraticDeterminantLIntegral
import SpectralRadiusUpperTail.RealSchurPairComplementDeterminant
import SpectralRadiusUpperTail.RealPairComplexRootData

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

theorem markedNonrealSylvester_abs_det (m : ℕ)
    (H : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : 0 < realPairHeightSq B) :
    |(realSchurRectangularSylvester H B).det| =
      ((H-realPairCenter B • 1)^2+(realPairHeight B)^2 • 1).det := by
  rw [realSchurRectangularSylvester_pair_abs_det m H B
    (realPair_nonreal_lower_entry_ne_zero B hB),← realPairHeight_sq B hB.le,
    abs_of_nonneg (real_quadratic_det_nonneg H (realPairCenter B) (realPairHeight B))]

theorem markedNonrealComplement_raw_moment (m : ℕ)
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : 0 < realPairHeightSq B) :
    (∫⁻ H : (Fin m × Fin m) → ℝ,
      ENNReal.ofReal (realMatrixGaussianWeight (Fin m) (Matrix.of H.curry))*
        ENNReal.ofReal |(realSchurRectangularSylvester (Matrix.of H.curry) B).det|) =
      realMatrixRawGaussianMass (Fin m)*
        ENNReal.ofReal ((m.factorial : ℝ)*
          ginibreExpPartial (m+1) ((realPairCenter B)^2+realPairHeightSq B)) := by
  simp_rw [markedNonrealSylvester_abs_det m _ B hB]
  change (∫⁻ H : (Fin m × Fin m) → ℝ,
    ENNReal.ofReal (Real.exp (-(∑ p, (H p)^2)/2))*
      ENNReal.ofReal (((Matrix.of H.curry-realPairCenter B • 1)^2+
        (realPairHeight B)^2 • 1).det))=_
  rw [gaussian_real_quadratic_det_raw_lintegral,realPairHeight_sq B hB.le,Fintype.card_fin]

theorem markedNonrealComplement_kernel_inner (m : ℕ) (g : ℂ → ℝ≥0∞)
    (B : (Fin 2 × Fin 2) → ℝ) :
    (∫⁻ H : (Fin m × Fin m) → ℝ, markedNonrealPairComplementKernel m g (B,H)) =
      (ENNReal.ofReal (realMatrixGaussianWeight (Fin 2) (Matrix.of B.curry))*
        markedNonrealBlockWeight (Matrix.of B.curry) g)*
          (realMatrixRawGaussianMass (Fin m)*ENNReal.ofReal ((m.factorial : ℝ)*
            ginibreExpPartial (m+1) ((realPairCenter (Matrix.of B.curry))^2+
              realPairHeightSq (Matrix.of B.curry)))) := by
  by_cases hB : 0 < realPairHeightSq (Matrix.of B.curry)
  · let f := fun H : (Fin m × Fin m) → ℝ =>
      ENNReal.ofReal (realMatrixGaussianWeight (Fin m) (Matrix.of H.curry))*
        ENNReal.ofReal |(realSchurRectangularSylvester (Matrix.of H.curry)
          (Matrix.of B.curry)).det|
    have hf : Measurable f := by
      have hc : Continuous (fun H : (Fin m × Fin m) → ℝ =>
          realSchurRectangularSylvester (Matrix.of H.curry) (Matrix.of B.curry)) := by
        apply continuous_matrix
        intro i j
        unfold realSchurRectangularSylvester
        change Continuous (fun H : (Fin m × Fin m) → ℝ =>
          (if i.2=j.2 then H (i.1,j.1) else 0)-
            (if i.1=j.1 then B (j.2,i.2) else 0))
        split_ifs <;> fun_prop
      have hw : Measurable (fun H : (Fin m × Fin m) → ℝ =>
          ENNReal.ofReal (realMatrixGaussianWeight (Fin m) (Matrix.of H.curry))) := by
        unfold realMatrixGaussianWeight
        change Measurable (fun H : (Fin m × Fin m) → ℝ =>
          ENNReal.ofReal (Real.exp (-(∑ p, (H p)^2)/2)))
        fun_prop
      exact hw.mul hc.matrix_det.abs.measurable.ennreal_ofReal
    have he (H : (Fin m × Fin m) → ℝ) :
        markedNonrealPairComplementKernel m g (B,H)=
          (ENNReal.ofReal (realMatrixGaussianWeight (Fin 2) (Matrix.of B.curry))*
            markedNonrealBlockWeight (Matrix.of B.curry) g)*f H := by
      dsimp [markedNonrealPairComplementKernel,f]
      ac_rfl
    simp_rw [he]
    rw [lintegral_const_mul _ hf]
    congr 1
    exact markedNonrealComplement_raw_moment m (Matrix.of B.curry) hB
  · simp [markedNonrealPairComplementKernel,markedNonrealBlockWeight,hB]

#print axioms markedNonrealSylvester_abs_det
#print axioms markedNonrealComplement_raw_moment
#print axioms markedNonrealComplement_kernel_inner
end SpectralRadiusUpperTail
