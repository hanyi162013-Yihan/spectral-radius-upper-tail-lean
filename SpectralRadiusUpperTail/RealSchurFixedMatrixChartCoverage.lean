import SpectralRadiusUpperTail.RealSchurFixedMatrixRegularFrame
import SpectralRadiusUpperTail.RealSchurMixedRegularOpenLocus
import SpectralRadiusUpperTail.RealGaussianActualSimpleSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

/-- A simple-spectrum real matrix, in its original fixed coordinates,
belongs after a finite index reordering to one of the regular mixed-Schur
chart loci. The chart itself allows the orthogonal frame to vary. -/
theorem realMatrix_exists_reindexed_regular_chart_of_separable
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsep : A.charpoly.Separable) :
    ∃ s : List ℕ,
      (∀ k ∈ s, k = 1 ∨ k = 2) ∧
      ∃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
        Matrix.reindex e e A ∈
          realSchurMixedRegularChartLocus (realSchurListBlockSize s) := by
  obtain ⟨s, hs, e, c, hA⟩ :=
    realMatrix_exists_reindexed_regular_frame_of_separable A hsep
  refine ⟨s, hs, e, ?_⟩
  rw [hA]
  exact realSchurMixedRegularFrame_center_mem_locus c

/-- The union of the regular mixed-Schur chart loci covers the actual
real Gaussian matrix law almost surely, after a finite reindexing of
the original matrix entries. -/
theorem realGaussianMatrix_exists_reindexed_regular_chart_ae
    (n : ℕ) :
    ∀ᵐ x : (Fin n × Fin n) → ℝ ∂gaussianMatrixLaw n,
      ∃ s : List ℕ,
        (∀ k ∈ s, k = 1 ∨ k = 2) ∧
        ∃ e : Fin n ≃ RealSchurMixedCoord (realSchurListBlockSize s),
          Matrix.reindex e e (Matrix.of x.curry) ∈
            realSchurMixedRegularChartLocus (realSchurListBlockSize s) := by
  filter_upwards [realGaussianMatrix_charpoly_separable_ae n] with x hx
  exact realMatrix_exists_reindexed_regular_chart_of_separable
    (Matrix.of x.curry) hx

#print axioms realGaussianMatrix_exists_reindexed_regular_chart_ae
end SpectralRadiusUpperTail
