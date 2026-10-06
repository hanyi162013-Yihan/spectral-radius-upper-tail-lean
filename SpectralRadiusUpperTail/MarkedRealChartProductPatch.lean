import SpectralRadiusUpperTail.MarkedRealChartBranchPatches
import SpectralRadiusUpperTail.RealSchurMixedRegularPatchIntegration
import SpectralRadiusUpperTail.RealMatrixSimpleSpectrumOpen
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped Matrix

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- First-branch patches in the ambient matrix-root product. Unlike
matrix-only disjointification, this preserves distinct marks. -/
def markedRealProductFirstPatch (m : ℕ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) : Set (MarkedMatrix m × ℝ) :=
  markedRealChartBranch m (c k) \
    ⋃ j ∈ Finset.range k, markedRealChartBranch m (c j)

theorem measurableSet_markedRealProductFirstPatch (m : ℕ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    MeasurableSet (markedRealProductFirstPatch m c k) := by
  exact (isOpen_markedRealChartBranch m (c k)).measurableSet.diff
    (Finset.measurableSet_biUnion _ fun j _ =>
      (isOpen_markedRealChartBranch m (c j)).measurableSet)

/-- The marked matrix-root coordinate map of a regular two-block
Schur chart is continuous on the whole tangent space. -/
theorem continuous_markedRealChartMarkMap (m : ℕ)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    Continuous (fun t : RealSchurMixedTangent (markedRealTwoBlockSizes m) =>
      (c.chart t, markedRealScalar m (c.T+t.2.val))) := by
  let s := markedRealTwoBlockSizes m
  have hentry : Continuous
      (realSchurMixedRotatedEntryCoordinates s c.T c.Q c.orthogonal) :=
    (realSchurMixedOutputCoordinateEquiv s c.Q
      c.orthogonal).toContinuousLinearEquiv.continuous.comp
        (realSchurMixedEntryCoordinates_differentiable s c.T).continuous
  have hmatrix : Continuous (fun t : RealSchurMixedTangent s => c.chart t) := by
    have h := (realSchurMixedEntryEquiv s).symm.toContinuousLinearEquiv.continuous.comp
      hentry
    convert h using 1
    funext t
    change c.chart t = (realSchurMixedEntryEquiv s).symm
      (realSchurMixedRotatedEntryCoordinates s c.T c.Q c.orthogonal t)
    rw [realSchurMixedRotatedEntryCoordinates_eq,
      LinearEquiv.symm_apply_apply]
    exact (realSchurMixedRegularRotatedChart_apply s c.T c.regular
      c.Q c.orthogonal t).symm
  exact hmatrix.prodMk (by fun_prop)

#print axioms measurableSet_markedRealProductFirstPatch
#print axioms continuous_markedRealChartMarkMap
end SpectralRadiusUpperTail
