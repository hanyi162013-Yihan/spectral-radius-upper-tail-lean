import SpectralRadiusUpperTail.MarkedRealUpperRankMeasurable
import SpectralRadiusUpperTail.MarkedRealAngularRankArea
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The fixed angular branch is open; its definition has no dependence
on the scalar eigenvalue, complementary matrix, or upper row. -/
theorem isOpen_markedRealAngularPositiveSource (m : ℕ) :
    IsOpen (markedRealAngularPositiveSource m) := by
  let s := markedRealTwoBlockSizes m
  have hframe : Continuous (realSchurMixedAngularFrame s) := by
    exact NormedSpace.exp_continuous.comp
      (realSchurMixedSkewCLM s).continuous
  have hentry : Continuous
      (fun Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ =>
        Q (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)) := by
    fun_prop
  have hpositive : IsOpen
      {w : RealSchurMixedOrbitIndex s → ℝ |
        0 < (realSchurMixedAngularFrame s w)
          (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)} :=
    isOpen_lt continuous_const (hentry.comp hframe)
  exact (realSchurMixedAngularProjectionChart s).open_source.inter hpositive

theorem measurableSet_markedRealAngularRankProduct
    (m k : ℕ) (b : ℝ) :
    MeasurableSet
      (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b) := by
  have hprod :=
    (isOpen_markedRealAngularPositiveSource m).measurableSet.prod
      (measurableSet_markedRealUpperRankSource m k b)
  exact prod_le_borel_prod _ hprod

/-- The direct area formula now applies to a complete measurable
rank-layer product, without its own center-dependent patch boundaries. -/
theorem markedRealAngularRank_lintegral_full
    (m k : ℕ) (hm : 0 < m) (b : ℝ)
    (g : RealSchurMixedTangent (markedRealTwoBlockSizes m) → ℝ≥0∞) :
    (∫⁻ y in
      realSchurMixedEntryCoordinates (markedRealTwoBlockSizes m) 0 ''
        (markedRealAngularPositiveSource m ×ˢ
          markedRealUpperRankSource m k b),
      g y ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m)) =
    ∫⁻ x in (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperRankSource m k b),
      ENNReal.ofReal (
        |(markedRealComplement m x.2.val -
            markedRealScalar m x.2.val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
          |realSchurMixedAngularJacobian
            (markedRealTwoBlockSizes m) x.1|) *
        g (realSchurMixedEntryCoordinates
          (markedRealTwoBlockSizes m) 0 x)
        ∂realSchurMixedCoordinateVolume (markedRealTwoBlockSizes m) := by
  exact markedRealAngularRank_lintegral_image m k hm b _
    (measurableSet_markedRealAngularRankProduct m k b)
    (Subset.rfl) g

#print axioms isOpen_markedRealAngularPositiveSource
#print axioms measurableSet_markedRealAngularRankProduct
#print axioms markedRealAngularRank_lintegral_full
end SpectralRadiusUpperTail
