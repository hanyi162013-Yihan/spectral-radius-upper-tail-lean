import SpectralRadiusUpperTail.MarkedRealChartGlobalArea
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The actual unnormalized Gaussian integral of the simple real-root
count is a global countable sum of local two-block Schur integrals. The
remaining task is to evaluate the angular and complementary Gaussian
integrals and convert the result to the one-point density. -/
theorem markedReal_gaussian_global_area_formula
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ) :
    (∫⁻ y,
      markedRealSimpleRootCount m b
        ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
      ∑' k, ∫⁻ t in markedRealChartFirstSource m b c k,
        ENNReal.ofReal (
          |(markedRealComplement m ((c k).T+t.2.val) -
              markedRealScalar m ((c k).T+t.2.val) •
                (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
            |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
        ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord (markedRealTwoBlockSizes m))
            ((c k).T+t.2.val))
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  have hmat : Continuous (realMatrixGaussianWeight
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hcoord : Continuous (realSchurMixedGaussianCoordinateWeight
      (markedRealTwoBlockSizes m)) := by
    unfold realSchurMixedGaussianCoordinateWeight
    exact hmat.comp ((realSchurMixedEntryEquiv
      (markedRealTwoBlockSizes m)).symm.toContinuousLinearEquiv.continuous)
  have hg : Measurable (fun y : RealSchurMixedTangent
      (markedRealTwoBlockSizes m) =>
      ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y)) := by
    fun_prop
  have hsum := markedRealChart_lintegral_imageSum_eq_rootCount
    m hm b c hcover
      (fun y => ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
        (markedRealTwoBlockSizes m) y)) hg
  rw [← hsum]
  congr 1
  funext k
  have hlocal := markedRealChart_gaussian_lintegral_firstPatch
    m hm b c k (fun _ => (1 : ℝ≥0∞))
  simpa only [mul_one] using hlocal

/-- A fixed countable atlas satisfying the exact Gaussian root-count
area formula exists in every dimension at least two. -/
theorem exists_markedReal_gaussian_global_area_formula
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      (∫⁻ y,
        markedRealSimpleRootCount m b
          ((realSchurMixedEntryEquiv (markedRealTwoBlockSizes m)).symm y) *
        ENNReal.ofReal (realSchurMixedGaussianCoordinateWeight
          (markedRealTwoBlockSizes m) y)
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
        ∑' k, ∫⁻ t in markedRealChartFirstSource m b c k,
          ENNReal.ofReal (
            |(markedRealComplement m ((c k).T+t.2.val) -
                markedRealScalar m ((c k).T+t.2.val) •
                  (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
              |realSchurMixedAngularJacobian (markedRealTwoBlockSizes m) t.1|) *
          ENNReal.ofReal (realMatrixGaussianWeight
            (RealSchurMixedCoord (markedRealTwoBlockSizes m))
              ((c k).T+t.2.val))
          ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  obtain ⟨c,hcover⟩ := exists_markedRealIncidenceFirstPatch_cover m hm b
  exact ⟨c, markedReal_gaussian_global_area_formula m hm b c hcover⟩

#print axioms markedReal_gaussian_global_area_formula
#print axioms exists_markedReal_gaussian_global_area_formula
end SpectralRadiusUpperTail
