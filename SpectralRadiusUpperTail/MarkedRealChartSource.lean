import SpectralRadiusUpperTail.MarkedRealChartProductPatch
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped Matrix

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- The marked scalar of every local two-block Schur point is an actual
real characteristic root. -/
theorem markedRealChart_scalar_isRoot
    (m : ℕ) (hm : 0 < m)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (t : RealSchurMixedTangent (markedRealTwoBlockSizes m)) :
    (c.chart t).charpoly.IsRoot
      (markedRealScalar m (c.T+t.2.val)) := by
  rw [Polynomial.IsRoot]
  have hchart := realSchurMixedRegularRotatedChart_apply
    (markedRealTwoBlockSizes m) c.T c.regular c.Q c.orthogonal t
  change c.chart t = _ at hchart
  rw [hchart, markedRealTwoBlock_rotatedChart_charpoly_factor
    m hm c.T c.Q c.upper c.orthogonal t,
    Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  simp

/-- Source parameters assigned to the first branch for their marked
scalar, with simple spectrum and the cutoff enforced. -/
def markedRealChartFirstSource (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) : Set (RealSchurMixedTangent (markedRealTwoBlockSizes m)) :=
  (c k).chart.source ∩
    {t | ((c k).chart t,
      markedRealScalar m ((c k).T+t.2.val)) ∈
        markedRealProductFirstPatch m c k} ∩
    {t | ((c k).chart t).charpoly.Separable} ∩
    {t | b < markedRealScalar m ((c k).T+t.2.val)}

theorem measurableSet_markedRealChartFirstSource
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    MeasurableSet (markedRealChartFirstSource m b c k) := by
  have hmap := continuous_markedRealChartMarkMap m (c k)
  have hbranch : MeasurableSet
      {t : RealSchurMixedTangent (markedRealTwoBlockSizes m) |
        ((c k).chart t,
          markedRealScalar m ((c k).T+t.2.val)) ∈
            markedRealProductFirstPatch m c k} :=
    (measurableSet_markedRealProductFirstPatch m c k).preimage hmap.measurable
  have hsimple : MeasurableSet
      {t : RealSchurMixedTangent (markedRealTwoBlockSizes m) |
        ((c k).chart t).charpoly.Separable} :=
    ((isOpen_realMatrix_charpoly_separable
      (RealSchurMixedCoord (markedRealTwoBlockSizes m))).preimage
      hmap.fst).measurableSet
  have hcutoff : MeasurableSet
      {t : RealSchurMixedTangent (markedRealTwoBlockSizes m) |
        b < markedRealScalar m ((c k).T+t.2.val)} :=
    (isOpen_Ioi.preimage hmap.snd).measurableSet
  exact ((c k).chart.open_source.measurableSet.inter hbranch).inter hsimple
    |>.inter hcutoff

theorem markedRealChartFirstSource_subset_source
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    markedRealChartFirstSource m b c k ⊆ (c k).chart.source := by
  intro t ht
  exact ht.1.1.1

#print axioms markedRealChart_scalar_isRoot
#print axioms measurableSet_markedRealChartFirstSource
#print axioms markedRealChartFirstSource_subset_source
end SpectralRadiusUpperTail
