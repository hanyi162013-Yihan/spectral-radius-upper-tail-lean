import SpectralRadiusUpperTail.RealSchurFixedGaussianReindex
import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration
import SpectralRadiusUpperTail.RealGaussianFixedSchurIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix ENNReal

theorem realSchurFixedChartOutput_reindex {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape)) :
    Matrix.reindex c.indexEquiv c.indexEquiv
      (Matrix.of (realSchurFixedChartOutputEntries c t).curry) =
        (realSchurMixedEntryEquiv (realSchurListBlockSize c.shape)).symm
          (realSchurMixedRotatedEntryCoordinates
            (realSchurListBlockSize c.shape) c.frame.T c.frame.Q
            c.frame.orthogonal t) := by
  let s := realSchurListBlockSize c.shape
  let y := realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
    c.frame.orthogonal t
  let x := realSchurFixedChartOutputEntries c t
  apply (realSchurMixedEntryEquiv s).injective
  rw [← realSchurFixedToMixedTangent_eq_reindex c.indexEquiv x,
    ← realSchurFixedToMixedLinearEquiv_apply c.indexEquiv x]
  rw [LinearEquiv.apply_symm_apply]
  change (realSchurFixedToMixedLinearEquiv c.indexEquiv)
    ((realSchurFixedToMixedLinearEquiv c.indexEquiv).symm y) = y
  exact LinearEquiv.apply_symm_apply _ _

/-- The fixed-array Gaussian weight on every chart output depends only
on the block-upper matrix and not on its orthogonal frame. -/
theorem realGaussianMatrixWeight_fixedChartOutput {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape)) :
    realGaussianMatrixWeight n (realSchurFixedChartOutputEntries c t) =
      realMatrixGaussianWeight (RealSchurMixedCoord
        (realSchurListBlockSize c.shape)) (c.frame.T+t.2.val) := by
  let s := realSchurListBlockSize c.shape
  let y := realSchurMixedRotatedEntryCoordinates s c.frame.T c.frame.Q
    c.frame.orthogonal t
  calc
    realGaussianMatrixWeight n (realSchurFixedChartOutputEntries c t) =
        realMatrixGaussianWeight (RealSchurMixedCoord s)
          (Matrix.reindex c.indexEquiv c.indexEquiv
            (Matrix.of (realSchurFixedChartOutputEntries c t).curry)) :=
      realGaussianMatrixWeight_mixed_reindex c.indexEquiv _
    _ = realSchurMixedGaussianCoordinateWeight s y := by
      rw [realSchurFixedChartOutput_reindex]
      rfl
    _ = realMatrixGaussianWeight (RealSchurMixedCoord s)
          (c.frame.T+t.2.val) :=
      realSchurMixedGaussianCoordinateWeight_rotated_chart
        s c.frame.T c.frame.Q c.frame.orthogonal t

theorem realGaussianFixedDensity_fixedChartOutput {n : ℕ}
    (c : RealSchurFixedChartIndex n)
    (t : RealSchurMixedTangent (realSchurListBlockSize c.shape)) :
    realGaussianFixedDensity n (realSchurFixedChartOutputEntries c t) =
      ENNReal.ofReal
        (realMatrixGaussianWeight (RealSchurMixedCoord
          (realSchurListBlockSize c.shape)) (c.frame.T+t.2.val) /
          (Real.sqrt (2*Real.pi))^(n*n)) := by
  unfold realGaussianFixedDensity
  rw [realGaussianMatrixWeight_fixedChartOutput]

#print axioms realGaussianFixedDensity_fixedChartOutput
end SpectralRadiusUpperTail
