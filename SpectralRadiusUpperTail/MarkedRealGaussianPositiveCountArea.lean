import SpectralRadiusUpperTail.MarkedRealGaussianCountIdentification
import SpectralRadiusUpperTail.RealGaussianFixedSchurCountExpectation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The exact Gaussian expectation of the positive real exterior-root
count is a normalized sum of marked Schur chart integrals. This is the
global area formula before evaluating the complementary determinant
moment and angular integral. -/
theorem realGaussian_positiveCount_global_area_formula
    (m : ℕ) (hm : 0 < m) (r : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m
        (r * Real.sqrt ((m+1 : ℕ) : ℝ)) c k) = Set.univ) :
    ENNReal.ofReal
      (∫ a : (Fin (m+1) × Fin (m+1)) → ℝ,
        realGaussianExteriorCount (m+1) r 0 a
        ∂gaussianMatrixLaw (m+1)) =
      (∑' k, ∫⁻ t in markedRealChartFirstSource m
          (r * Real.sqrt ((m+1 : ℕ) : ℝ)) c k,
        ENNReal.ofReal (
          |(markedRealComplement m ((c k).T+t.2.val) -
              markedRealScalar m ((c k).T+t.2.val) •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
        ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m))
            ((c k).T+t.2.val))
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) /
      ENNReal.ofReal
        ((Real.sqrt (2*Real.pi))^
          ((Fintype.card
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2)) := by
  rw [← realGaussianExteriorCount_lintegral_eq_ofReal_expectation
    (m+1) (by omega) r 0]
  calc
    (∫⁻ a : (Fin (m+1) × Fin (m+1)) → ℝ,
      ENNReal.ofReal (realGaussianExteriorCount (m+1) r 0 a)
        ∂gaussianMatrixLaw (m+1)) =
      ∫⁻ a,
        markedRealSimpleRootCount m (r * Real.sqrt ((m+1 : ℕ) : ℝ))
          (Matrix.reindex (markedRealIndexEquiv m)
            (markedRealIndexEquiv m) (Matrix.of a.curry))
        ∂gaussianMatrixLaw (m+1) := by
      apply lintegral_congr_ae
      filter_upwards [markedRealSimpleRootCount_eq_exteriorCount_ae m hm r]
        with a ha
      exact ha.symm
    _ = _ := realGaussian_markedRootCount_global_area_formula
      m hm (r * Real.sqrt ((m+1 : ℕ) : ℝ)) c hcover

/-- The completely specified chart-side value in the Gaussian
positive-real root-count area formula. -/
noncomputable def realGaussianPositiveCountSchurArea
    (m : ℕ) (r : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) : ℝ≥0∞ :=
  (∑' k, ∫⁻ t in markedRealChartFirstSource m
      (r * Real.sqrt ((m+1 : ℕ) : ℝ)) c k,
    ENNReal.ofReal (
      |(markedRealComplement m ((c k).T+t.2.val) -
          markedRealScalar m ((c k).T+t.2.val) •
            (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
    ENNReal.ofReal (realMatrixGaussianWeight
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        ((c k).T+t.2.val))
    ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) /
  ENNReal.ofReal
    ((Real.sqrt (2*Real.pi))^
      ((Fintype.card
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)))^2))

/-- An unconditional global chart representation for the actual
positive-real Gaussian eigenvalue count exists in each dimension at
least two. The chart integral still awaits explicit evaluation. -/
theorem exists_realGaussian_positiveCountSchurArea
    (m : ℕ) (hm : 0 < m) (r : ℝ) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      ENNReal.ofReal
        (∫ a : (Fin (m+1) × Fin (m+1)) → ℝ,
          realGaussianExteriorCount (m+1) r 0 a
          ∂gaussianMatrixLaw (m+1)) =
        realGaussianPositiveCountSchurArea m r c := by
  obtain ⟨c,hcover⟩ := exists_markedRealIncidenceFirstPatch_cover m hm
    (r * Real.sqrt ((m+1 : ℕ) : ℝ))
  refine ⟨c, ?_⟩
  exact realGaussian_positiveCount_global_area_formula m hm r c hcover

/-- One countable marked-root atlas works for every positive-real cutoff.
In particular, the chart family is chosen before the radius parameter. -/
theorem exists_realGaussian_positiveCountSchurArea_allCutoffs
    (m : ℕ) (hm : 0 < m) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      ∀ r : ℝ,
        ENNReal.ofReal
          (∫ a : (Fin (m+1) × Fin (m+1)) → ℝ,
            realGaussianExteriorCount (m+1) r 0 a
            ∂gaussianMatrixLaw (m+1)) =
          realGaussianPositiveCountSchurArea m r c := by
  obtain ⟨c,hc⟩ := exists_markedRealChartBranch_sequence m hm
  refine ⟨c, ?_⟩
  intro r
  apply realGaussian_positiveCount_global_area_formula m hm r c
  rw [iUnion_markedRealIncidenceFirstPatch]
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨k,hk⟩ := hc p.val.1 p.val.2 p.property.1 p.property.2.1
  exact ⟨k,hk⟩

#print axioms realGaussian_positiveCount_global_area_formula
#print axioms exists_realGaussian_positiveCountSchurArea
#print axioms exists_realGaussian_positiveCountSchurArea_allCutoffs
end SpectralRadiusUpperTail
