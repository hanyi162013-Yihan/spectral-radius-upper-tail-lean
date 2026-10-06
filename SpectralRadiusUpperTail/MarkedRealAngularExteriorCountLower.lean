import SpectralRadiusUpperTail.MarkedRealAngularActualCountLower
import SpectralRadiusUpperTail.MarkedRealGaussianPositiveCountArea
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix

/-- The normalized contribution from one angular branch, expressed
through the actual complementary Gaussian characteristic polynomial. -/
noncomputable def markedRealAngularLocalCountLower (m : ℕ) (b : ℝ) : ℝ≥0∞ :=
  ((∫⁻ ω, markedRealAngularWeight m ω) *
      (∫⁻ x : ℝ,
        if b < x then
          ENNReal.ofReal (Real.exp (-x^2/2)) *
            ENNReal.ofReal ((Real.sqrt (2*Real.pi))^(m^2+m)) *
            markedRealGaussianCharpolyMoment m x
        else 0)) *
    (ENNReal.ofReal ((Real.sqrt (2*Real.pi))^
      ((Fintype.card
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)))⁻¹

/-- In actual iid Gaussian matrices, the positive-real exterior-root
expectation dominates the explicitly evaluated single-chart term. -/
theorem markedRealAngularLocalCountLower_le_positiveCount
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    markedRealAngularLocalCountLower m
        (r * Real.sqrt ((m+1 : ℕ) : ℝ)) ≤
      ENNReal.ofReal
        (∫ a : (Fin (m+1) × Fin (m+1)) → ℝ,
          realGaussianExteriorCount (m+1) r 0 a
          ∂gaussianMatrixLaw (m+1)) := by
  rw [← realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    (m+1) (by omega) r 0]
  calc
    markedRealAngularLocalCountLower m
        (r * Real.sqrt ((m+1 : ℕ) : ℝ)) ≤
      ∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
        markedRealSimpleRootCount m
          (r * Real.sqrt ((m+1 : ℕ) : ℝ))
          (Matrix.reindex (markedRealIndexEquiv m)
            (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1) := by
      exact markedRealAngular_gaussianMoment_le_actualRootCount
        m hm (r * Real.sqrt ((m+1 : ℕ) : ℝ))
    _ = ∫⁻ a,
        ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a)
        ∂gaussianMatrixLaw (m+1) := by
      apply lintegral_congr_ae
      filter_upwards [markedRealSimpleRootCount_eq_exteriorCount_ae m hm r]
        with a ha
      exact ha

#print axioms markedRealAngularLocalCountLower_le_positiveCount
end SpectralRadiusUpperTail
