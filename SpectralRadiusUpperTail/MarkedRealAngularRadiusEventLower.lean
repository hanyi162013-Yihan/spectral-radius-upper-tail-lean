import SpectralRadiusUpperTail.MarkedRealAngularExteriorCountLower
import SpectralRadiusUpperTail.SpectralMeasurable
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix

/-- The explicit local characteristic-polynomial term is also a
finite-dimensional lower bound for the Gaussian spectral-radius event,
up to the elementary factor given by the matrix dimension. -/
theorem markedRealAngularLocalCountLower_le_radiusEvent
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    markedRealAngularLocalCountLower m
        (r * Real.sqrt ((m+1 : ℕ) : ℝ)) ≤
      (m+1 : ℝ≥0∞) *
        gaussianMatrixLaw (m+1)
          {a : (Fin (m+1) × Fin (m+1)) → ℝ |
            r < realMatrixRadius
              ((1/Real.sqrt ((m+1 : ℕ) : ℝ)) • entryMatrix a)} := by
  let E : Set ((Fin (m+1) × Fin (m+1)) → ℝ) :=
    {a | r < realMatrixRadius
      ((1/Real.sqrt ((m+1 : ℕ) : ℝ)) • entryMatrix a)}
  have hE : MeasurableSet E := by
    letI : MeasurableSpace (Matrix (Fin (m+1)) (Fin (m+1)) ℝ) :=
      finiteMatrixMeasurableSpace (m+1) (m+1) ℝ
    exact measurableSet_lt measurable_const
      (realMatrixRadius_measurable.comp
        (scaled_entryMatrix_continuous
          (1/Real.sqrt ((m+1 : ℕ) : ℝ))).measurable)
  have hpoint (a : (Fin (m+1) × Fin (m+1)) → ℝ) :
      ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a) ≤
        (m+1 : ℝ≥0∞) * E.indicator (fun _ => (1 : ℝ≥0∞)) a := by
    have hb := realGaussianExteriorCount_bounds (m+1) r 0 a
    by_cases hp : 0 < realGaussianExteriorCount (m+1) r 0 a
    · have he : a ∈ E :=
        (realGaussianExteriorCount_cover (m+1) (by omega) r a).2
          (Or.inl hp)
      simp only [indicator, he, if_pos, mul_one]
      exact_mod_cast hb.2.2
    · have hz : realGaussianExteriorCount (m+1) r 0 a = 0 :=
        le_antisymm (le_of_not_gt hp) hb.1
      simp [hz]
  have hcount := markedRealAngularLocalCountLower_le_positiveCount
    m hm r
  rw [← realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    (m+1) (by omega) r 0] at hcount
  calc
    markedRealAngularLocalCountLower m
        (r * Real.sqrt ((m+1 : ℕ) : ℝ)) ≤
      ∫⁻ a,
        ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a)
        ∂gaussianMatrixLaw (m+1) := hcount
    _ ≤ ∫⁻ a, (m+1 : ℝ≥0∞) *
        E.indicator (fun _ => (1 : ℝ≥0∞)) a
        ∂gaussianMatrixLaw (m+1) := lintegral_mono hpoint
    _ = (m+1 : ℝ≥0∞) * gaussianMatrixLaw (m+1) E := by
      rw [lintegral_const_mul _ (measurable_const.indicator hE)]
      simp [lintegral_indicator hE]

#print axioms markedRealAngularLocalCountLower_le_radiusEvent
end SpectralRadiusUpperTail
