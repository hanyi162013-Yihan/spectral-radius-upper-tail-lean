import SpectralRadiusUpperTail.RealSchurFiniteAtlas
import SpectralRadiusUpperTail.RealSchurFixedFlagFiber
import SpectralRadiusUpperTail.RealSchurFixedGaussianChartWeight

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator ENNReal

theorem RealSchurFiniteAtlas.output_reindex {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) :
    Matrix.reindex I.2.1 I.2.1 (Matrix.of (F.output I k t).curry) =
      (realSchurMixedEntryEquiv I.1.sizes).symm
        (realSchurMixedRotatedEntryCoordinates I.1.sizes 0
          (F.frames I k).val (F.frames I k).property t) := by
  apply (realSchurMixedEntryEquiv I.1.sizes).injective
  rw [← realSchurFixedToMixedTangent_eq_reindex I.2.1,
    ← realSchurFixedToMixedLinearEquiv_apply I.2.1]
  rw [LinearEquiv.apply_symm_apply]
  exact LinearEquiv.apply_symm_apply _ _

theorem RealSchurFiniteAtlas.output_matrix {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) :
    Matrix.of (F.output I k t).curry =
      Matrix.reindex I.2.1.symm I.2.1.symm
        ((F.frames I k).val * realSchurMixedExpCoordinates I.1.sizes 0 t *
          (F.frames I k).valᵀ) := by
  have h := F.output_reindex I k t
  rw [realSchurMixedRotatedEntryCoordinates_eq,LinearEquiv.symm_apply_apply] at h
  apply (Matrix.reindexLinearEquiv ℝ ℝ I.2.1 I.2.1).injective
  change Matrix.reindex I.2.1 I.2.1 (Matrix.of (F.output I k t).curry)=_
  rw [h]
  ext i j
  simp [Matrix.reindex_apply]

theorem RealSchurFiniteAtlas.output_fiber {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (w : RealSchurMixedOrbitIndex I.1.sizes → ℝ)
    (d : RealSchurMixedDiagonalEntry I.1.sizes → ℝ)
    (u : RealSchurMixedStrictUpperEntry I.1.sizes → ℝ) :
    Matrix.of (F.output I k (realSchurMixedFiberPoint I.1.sizes w d u)).curry =
      realSchurFixedFlagFiberMatrix I.1.sizes I.2.1 (F.frames I k) d (w,u) :=
  F.output_matrix I k _

theorem RealSchurFiniteAtlas.output_gaussianWeight {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) :
    realGaussianMatrixWeight n (F.output I k t) =
      realMatrixGaussianWeight (RealSchurMixedCoord I.1.sizes) t.2.val := by
  rw [realGaussianMatrixWeight_mixed_reindex I.2.1,F.output_reindex]
  change realSchurMixedGaussianCoordinateWeight I.1.sizes
    (realSchurMixedRotatedEntryCoordinates I.1.sizes 0
      (F.frames I k).val (F.frames I k).property t)=_
  rw [realSchurMixedGaussianCoordinateWeight_rotated_chart,zero_add]

theorem RealSchurFiniteAtlas.output_density {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) :
    realGaussianFixedDensity n (F.output I k t) =
      ENNReal.ofReal (realMatrixGaussianWeight (RealSchurMixedCoord I.1.sizes) t.2.val /
        (Real.sqrt (2*Real.pi))^(n*n)) := by
  unfold realGaussianFixedDensity
  rw [F.output_gaussianWeight]

#print axioms RealSchurFiniteAtlas.output_reindex
#print axioms RealSchurFiniteAtlas.output_matrix
#print axioms RealSchurFiniteAtlas.output_fiber
#print axioms RealSchurFiniteAtlas.output_gaussianWeight
#print axioms RealSchurFiniteAtlas.output_density
end SpectralRadiusUpperTail
